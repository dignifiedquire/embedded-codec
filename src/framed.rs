use embedded_io_async::{Read, Write, ErrorType, ErrorKind};

use crate::{Buffer, Decoder, Stream, Encoder, Sink};

pub struct Framed<'a, RW, Codec, const N: usize> {
    inner: RW,
    codec: Codec,
    read_frame: ReadFrame<'a, N>,
    write_frame: WriteFrame<'a, N>,
}

struct ReadFrame<'a, const N: usize> {
    buffer: Buffer<'a, N>,
    eof: bool,
    is_readable: bool,
    has_errored: bool,
}

struct WriteFrame<'a, const N: usize> {
    buffer: Buffer<'a, N>,
    backpressure_boundary: usize,
}

impl<RW, Codec, const N: usize> Stream for Framed<'_, RW, Codec, N>
where
    RW: Read + Write,
    Codec: Decoder,
    Codec::Error: From<<RW as ErrorType>::Error>,
{
    type Item = Result<Codec::Item, Codec::Error>;

    async fn next(&mut self) -> Option<Self::Item> {
        let state = &mut self.read_frame;
        // The following loops implements a state machine with each state corresponding
        // to a combination of the `is_readable` and `eof` flags. States persist across
        // loop entries and most state transitions occur with a return.
        //
        // The initial state is `reading`.
        //
        // | state   | eof   | is_readable | has_errored |
        // |---------|-------|-------------|-------------|
        // | reading | false | false       | false       |
        // | framing | false | true        | false       |
        // | pausing | true  | true        | false       |
        // | paused  | true  | false       | false       |
        // | errored | <any> | <any>       | true        |
        //                                                       `decode_eof` returns Err
        //                                          ┌────────────────────────────────────────────────────────┐
        //                   `decode_eof` returns   │                                                        │
        //                             `Ok(Some)`   │                                                        │
        //                                 ┌─────┐  │     `decode_eof` returns               After returning │
        //                Read 0 bytes     ├─────▼──┴┐    `Ok(None)`          ┌────────┐ ◄───┐ `None`    ┌───▼─────┐
        //               ┌────────────────►│ Pausing ├───────────────────────►│ Paused ├─┐   └───────────┤ Errored │
        //               │                 └─────────┘                        └─┬──▲───┘ │               └───▲───▲─┘
        // Pending read  │                                                      │  │     │                   │   │
        //     ┌──────┐  │            `decode` returns `Some`                   │  └─────┘                   │   │
        //     │      │  │                   ┌──────┐                           │  Pending                   │   │
        //     │ ┌────▼──┴─┐ Read n>0 bytes ┌┴──────▼─┐     read n>0 bytes      │  read                      │   │
        //     └─┤ Reading ├───────────────►│ Framing │◄────────────────────────┘                            │   │
        //       └──┬─▲────┘                └─────┬──┬┘                                                      │   │
        //          │ │                           │  │                 `decode` returns Err                  │   │
        //          │ └───decode` returns `None`──┘  └───────────────────────────────────────────────────────┘   │
        //          │                             read returns Err                                               │
        //          └────────────────────────────────────────────────────────────────────────────────────────────┘
        loop {
            // Return `None` if we have encountered an error from the underlying decoder
            if state.has_errored {
                // preparing has_errored -> paused
                state.is_readable = false;
                state.has_errored = false;
                return None;
            }

            // Repeatedly call `decode` or `decode_eof` while the buffer is "readable",
            // i.e. it _might_ contain data consumable as a frame or closing frame.
            // Both signal that there is no such data by returning `None`.
            //
            // If `decode` couldn't read a frame and the upstream source has returned eof,
            // `decode_eof` will attempt to decode the remaining bytes as closing frames.
            //
            // If the underlying Read is resumable, we may continue after an EOF,
            // but must finish emitting all of it's associated `decode_eof` frames.
            // Furthermore, we don't want to emit any `decode_eof` frames on retried
            // reads after an EOF unless we've actually read more data.
            if state.is_readable {
                // pausing or framing
                if state.eof {
                    // pausing
                    match self.codec.decode_eof(&mut state.buffer) {
                        Ok(Some(frame)) => {
                            // implicit pausing -> pausing or pausing -> paused
                            return Some(Ok(frame));
                        }
                        Ok(None) => {
                            state.is_readable = false; // prepare pausing -> paused
                        }
                        Err(err) => {
                            state.has_errored = true;
                            return Some(Err(err));
                        }
                    }
                }

                // framing
                match self.codec.decode(&mut state.buffer) {
                    Ok(Some(frame)) => {
                        // implicit framing -> framing
                        return Some(Ok(frame));
                    }
                    Ok(None) => {}
                    Err(err) => {
                        state.has_errored = true;
                        return Some(Err(err));
                    }
                }

                // framing -> reading
                state.is_readable = false;
            }
            // reading or paused
            // If we can't build a frame yet, try to read more data and try again.
            // Make sure we've got room for at least one byte to read to ensure
            // that we don't get a spurious 0 that looks like EOF.
            if state.buffer.remaining_mut() == 0 {
                return Some(Err(ErrorKind::OutOfMemory.into()));
            }
            let chunk = state.buffer.chunk_mut();
            let bytect = match self.inner.read(chunk).await {
                Ok(n) => {
                    state.buffer.advance_mut(n);
                    n
                },
                Err(err) => {
                    state.has_errored = true;
                    return Some(Err(err.into()));
                }
            };
            if bytect == 0 {
                if state.eof {
                    // We're already at an EOF, and since we've reached this path
                    // we're also not readable. This implies that we've already finished
                    // our `decode_eof` handling, so we can simply return `None`.
                    // implicit paused -> paused
                    return None;
                }
                // prepare reading -> paused
                state.eof = true;
            } else {
                // prepare paused -> framing or noop reading -> framing
                state.eof = false;
            }

            // paused -> framing or reading -> framing or reading -> pausing
            state.is_readable = true;
        }
    }
}

impl<RW, Codec, const N: usize> ErrorType for Framed<'_, RW, Codec, N>
where
    RW: Read + Write,
    Codec: ErrorType,
{
    type Error = Codec::Error;
}

impl<RW, Codec, I, const N: usize> Sink<I> for Framed<'_, RW, Codec, N>
where
    RW: Read + Write,
    Codec: Encoder<I>,
    Codec::Error: From<<RW as ErrorType>::Error>,
{
    async fn send(&mut self, item: I) -> Result<(), Self::Error> {
        self.codec.encode(item, &mut self.write_frame.buffer)?;
        while self.write_frame.buffer.remaining() > 0 {
            let n = self.inner.write(self.write_frame.buffer.chunk()).await?;
            self.write_frame.buffer.advance(n);
        }

        if self.write_frame.buffer.remaining() >= self.write_frame.backpressure_boundary  {
            self.inner.flush().await?;
        }

        Ok(())
    }

    async fn flush(&mut self) -> Result<(), Self::Error> {
        // write out any remaining data in the out_buffer
        while self.write_frame.buffer.remaining() > 0 {
            let n = self.inner.write(self.write_frame.buffer.chunk()).await?;
            self.write_frame.buffer.advance(n);
        }

        self.inner.flush().await?;
        Ok(())
    }

    async fn close(&mut self) -> Result<(), Self::Error> {
        self.inner.flush().await?;

        // can we do sth here?
        Ok(())
    }
}
