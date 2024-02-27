use bytes::BytesMut;
use embedded_io_async::ErrorType;

pub trait Encoder<Item>: ErrorType {
    /// Encode the given item, returning how many bytes have been written.
    fn encode(&mut self, item: Item, dst: &mut BytesMut) -> Result<(), Self::Error>;

    /// Returns the encoded length of the item, if available.
    fn encode_len(&self, _item: &Item) -> Option<usize> {
        None
    }
}
