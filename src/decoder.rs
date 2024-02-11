use embedded_io_async::ErrorType;

use crate::buffer::Buffer;

pub trait Decoder: ErrorType {
    type Item;

    /// Returns a valid item if possible and how much of `src` was consumed.
    fn decode<const N: usize>(
        &mut self,
        src: &mut Buffer<'_, N>,
    ) -> Result<Option<Self::Item>, Self::Error>;
}
