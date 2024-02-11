use embedded_io_async::{Read, Write, ErrorType};

use crate::{Buffer, Decoder, Stream, Encoder, Sink};

pub struct Framed<'a, RW, Codec, const N: usize> {
    inner: RW,
    codec: Codec,
    /// Buffer for reading.
    in_buffer: Buffer<'a, N>,
    /// Buffer for writing.
    out_buffer: Buffer<'a, N>,
    state_is_eof: bool,
    state_has_errored: bool,
}

impl<RW, Codec, const N: usize> Stream for Framed<'_, RW, Codec, N>
where
    RW: Read + Write,
    Codec: Decoder,
    Codec::Error: From<<RW as ErrorType>::Error>,
{
    type Item = Result<Codec::Item, Codec::Error>;

    async fn next(&mut self) -> Option<Self::Item> {
        if self.state_is_eof || self.state_has_errored {
            return None;
        }

        loop {
            // check if we already have enough in our buffer
            match self.codec.decode(&mut self.in_buffer) {
                Ok(Some(item)) => {
                    return Some(Ok(item));
                }
                Ok(None) => {
                    // Not enough yet

                    // read until enough from inner
                    let chunk = self.in_buffer.chunk_mut();
                    match self.inner.read(chunk).await {
                        Ok(n) => {
                            if n == 0 {
                                self.state_is_eof = true;
                            }
                            self.in_buffer.advance_mut(n);
                        }
                        Err(err) => {
                            self.state_has_errored = true;
                            return Some(Err(err.into()));
                        }
                    }
                }
                Err(err) => {
                    self.state_has_errored = true;
                    return Some(Err(err));
                }
            }
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
        self.codec.encode(item, &mut self.out_buffer)?;
        while self.out_buffer.remaining() > 0 {
            let n = self.inner.write(self.out_buffer.chunk()).await?;
            self.out_buffer.advance(n);
        }

        Ok(())
    }

    async fn flush(&mut self) -> Result<(), Self::Error> {
        self.inner.flush().await?;
        Ok(())
    }

    async fn close(&mut self) -> Result<(), Self::Error> {
        self.inner.flush().await?;

        // can we do sth here?
        Ok(())
    }
}
