use embedded_io_async::ErrorType;

use crate::buffer::Buffer;

pub trait Encoder<Item>: ErrorType {
    /// Encode the given item, returning how many bytes have been written.
    fn encode<const N: usize>(
        &mut self,
        item: Item,
        dst: &mut Buffer<'_, N>,
    ) -> Result<(), Self::Error>;

    /// Returns the encoded length of the item, if available.
    fn encode_len(&self, _item: &Item) -> Option<usize> {
        None
    }
}
