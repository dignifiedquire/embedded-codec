use embedded_io_async::ErrorType;

/// Equivalent of the poll based `futures::Sink` trait.
pub trait Sink<Item>: ErrorType {
    async fn send(&mut self, item: Item) -> Result<(), Self::Error>;
    async fn flush(&mut self) -> Result<(), Self::Error>;
    async fn close(&mut self) -> Result<(), Self::Error>;
}
