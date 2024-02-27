use core::{cmp, fmt, str, usize};

use bytes::{Buf, BufMut, BytesMut};
use embedded_io_async::{Error, ErrorKind, ErrorType};

use crate::decoder::Decoder;
use crate::encoder::Encoder;

/// A simple [`Decoder`] and [`Encoder`] implementation that splits up data into lines.
///
/// This uses the `\n` character as the line ending on all platforms.
///
/// [`Decoder`]: crate::codec::Decoder
/// [`Encoder`]: crate::codec::Encoder
#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct LinesCodec {
    // Stored index of the next index to examine for a `\n` character.
    // This is used to optimize searching.
    // For example, if `decode` was called with `abc`, it would hold `3`,
    // because that is the next index to examine.
    // The next time `decode` is called with `abcde\n`, the method will
    // only look at `de\n` before returning.
    next_index: usize,

    /// The maximum length for a given line. If `usize::MAX`, lines will be
    /// read until a `\n` character is reached.
    max_length: usize,

    /// Are we currently discarding the remainder of a line which was over
    /// the length limit?
    is_discarding: bool,
}

impl LinesCodec {
    /// Returns a `LinesCodec` with a maximum line length limit.
    ///
    /// Calls to `LinesCodec::decode` will return a
    /// [`LinesCodecError`] when a line exceeds the length limit. Subsequent calls
    /// will discard up to `limit` bytes from that line until a newline
    /// character is reached, returning `None` until the line over the limit
    /// has been fully discarded. After that point, calls to `decode` will
    /// function as normal.
    ///
    /// [`LinesCodecError`]: crate::codec::LinesCodecError
    pub fn new_with_max_length(max_length: usize) -> Self {
        LinesCodec {
            max_length,
            next_index: 0,
            is_discarding: false,
        }
    }

    /// Returns the maximum line length when decoding.
    pub fn max_length(&self) -> usize {
        self.max_length
    }
}

fn utf8(buf: &[u8]) -> Result<&str, ErrorKind> {
    str::from_utf8(buf).map_err(|_| ErrorKind::InvalidData)
}

fn without_carriage_return(s: &[u8]) -> &[u8] {
    if let Some(&b'\r') = s.last() {
        &s[..s.len() - 1]
    } else {
        s
    }
}

impl Decoder for LinesCodec {
    type Item = String;
    type Error = LinesCodecError;

    fn decode(&mut self, buf: &mut BytesMut) -> Result<Option<String>, LinesCodecError> {
        // Determine how far into the buffer we'll search for a newline.
        loop {
            let chunk = buf.chunk();
            let read_to = cmp::min(chunk.len(), self.max_length.saturating_add(1));
            let newline_offset = chunk[self.next_index..read_to]
                .iter()
                .position(|b| *b == b'\n');

            match (self.is_discarding, newline_offset) {
                (true, Some(offset)) => {
                    // If we found a newline, discard up to that offset and
                    // then stop discarding. On the next iteration, we'll try
                    // to read a line normally.
                    buf.advance(offset + self.next_index + 1);
                    self.is_discarding = false;
                    self.next_index = 0;
                }
                (true, None) => {
                    // Otherwise, we didn't find a newline, so we'll discard
                    // everything we read. On the next iteration, we'll continue
                    // discarding up to max_len bytes unless we find a newline.
                    buf.advance(read_to);
                    self.next_index = 0;
                    if buf.is_empty() {
                        return Ok(None);
                    }
                }
                (false, Some(offset)) => {
                    // Found a line!
                    let newline_index = offset + self.next_index;
                    self.next_index = 0;
                    let line = buf.split_to(newline_index + 1);
                    let line = &line[..line.len() - 1];
                    let line = without_carriage_return(line);
                    let line = utf8(line)?;
                    return Ok(Some(line.to_string()));
                }
                (false, None) if buf.len() > self.max_length => {
                    // Reached the maximum length without finding a
                    // newline, return an error and start discarding on the
                    // next call.
                    self.is_discarding = true;
                    return Err(LinesCodecError::MaxLineLengthExceeded);
                }
                (false, None) => {
                    // We didn't find a line or reach the length limit, so the next
                    // call will resume searching at the current offset.
                    self.next_index = read_to;
                    return Ok(None);
                }
            }
        }
    }

    fn decode_eof(&mut self, buf: &mut BytesMut) -> Result<Option<String>, LinesCodecError> {
        Ok(match self.decode(buf)? {
            Some(frame) => Some(frame),
            None => {
                // No terminating newline - return remaining data, if any
                if buf.is_empty() || buf.chunk() == &b"\r"[..] {
                    None
                } else {
                    let line = buf.split_to(buf.len());
                    let line = without_carriage_return(&line);
                    let line = utf8(line)?;
                    self.next_index = 0;
                    Some(line.to_string())
                }
            }
        })
    }
}

impl ErrorType for LinesCodec {
    type Error = LinesCodecError;
}

impl<T> Encoder<T> for LinesCodec
where
    T: AsRef<str>,
{
    fn encode(&mut self, line: T, buf: &mut BytesMut) -> Result<(), LinesCodecError> {
        let line = line.as_ref();
        buf.reserve(line.len() + 1);
        buf.put(line.as_bytes());
        buf.put_u8(b'\n');
        Ok(())
    }

    fn encode_len(&self, line: &T) -> Option<usize> {
        let line = line.as_ref();
        Some(line.len() + 1)
    }
}

/// An error occurred while encoding or decoding a line.
#[derive(Debug)]
pub enum LinesCodecError {
    /// The maximum line length was exceeded.
    MaxLineLengthExceeded,
    /// An IO error occurred.
    Io(ErrorKind),
}

impl Error for LinesCodecError {
    fn kind(&self) -> ErrorKind {
        match self {
            Self::MaxLineLengthExceeded => ErrorKind::InvalidInput,
            Self::Io(kind) => *kind,
        }
    }
}

impl fmt::Display for LinesCodecError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LinesCodecError::MaxLineLengthExceeded => write!(f, "max line length exceeded"),
            LinesCodecError::Io(e) => write!(f, "{:?}", e),
        }
    }
}

impl From<ErrorKind> for LinesCodecError {
    fn from(e: ErrorKind) -> LinesCodecError {
        LinesCodecError::Io(e)
    }
}

#[cfg(feature = "std")]
impl std::error::Error for LinesCodecError {}
