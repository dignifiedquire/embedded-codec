/// Equivalent of the poll based `futures::Stream` trait.
pub trait Stream {
    type Item;

    async fn next(&mut self) -> Option<Self::Item>;

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, None)
    }
}
