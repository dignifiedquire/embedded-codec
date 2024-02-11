pub struct Buffer<'a, const N: usize> {
    storage: BufferStorage<'a, N>,
    start: usize,
    end: usize,
}

impl<'a, const N: usize> Buffer<'a, N> {
    pub fn from_storage(storage: BufferStorage<'a, N>) -> Self {
        Self {
            storage,
            start: 0,
            end: 0,
        }
    }

    pub fn remaining(&self) -> usize {
        if self.end >= self.start {
            // [0...start...end...len]
            self.end - self.start
        } else {
            if self.start < self.storage.len() {
                // [0...end...start...len]
                (self.storage.len() - self.start) + self.end
            } else {
                // [0...end...start = len]
                self.end
            }
        }
    }

    pub fn remaining_mut(&self) -> usize {
        if dbg!(self.end >= self.start) {
            if dbg!(self.end) < dbg!(self.storage.len()) {
                // [0...start...end...len]
                self.storage.len() - self.end
            } else {
                // [0...start...end = len]
                self.start
            }
        } else {
            // [0...end...start...len]
            self.start - self.end
        }
    }

    pub fn chunk_mut(&mut self) -> &mut [u8] {
        if self.end >= self.start {
            if self.end < self.storage.len() {
                // [0...start...end...len]
                &mut self.storage[self.end..]
            } else {
                // [0...start...end = len]
                &mut self.storage[..self.start]
            }
        } else {
            // [0...end...start...len]
            &mut self.storage[self.end..self.start]
        }
    }

    pub fn advance_mut(&mut self, cnt: usize) {
        if self.end >= self.start {
            if self.end < self.storage.len() {
                // [0...start...end...len]
                assert!(cnt <= self.storage.len() - self.end);
                self.end += cnt;
            } else {
                // [0...start...end = len]
                assert!(cnt <= self.start);
                self.end = cnt;
            }
        } else {
            // [0...end...start...len]
            assert!(self.end + cnt <= self.start);
            self.end += cnt;
        }
    }

    /// Advances the start cursor.
    pub fn advance(&mut self, cnt: usize) {
        if self.end >= self.start {
            // [0...start...end...len]
            assert!(self.start + cnt <= self.end);
            self.start += cnt;
        } else {
            if self.start < self.storage.len() {
                // [0...end...start...len]
                assert!(self.start + cnt <= self.storage.len());
                self.start += cnt;
            } else {
                // [0...end...start = len]
                assert!(cnt <= self.end);
                self.start = cnt;
            }
        }
    }

    pub fn chunk(&self) -> &[u8] {
        if self.end >= self.start {
            // [0...start...end...len]
            &self.storage[self.start..self.end]
        } else {
            if self.start < self.storage.len() {
                // [0...end...start...len]
                &self.storage[self.start..]
            } else {
                // [0...end...start = len]
                &self.storage[..self.end]
            }
        }
    }
}

/// Flexible buffer backend to allow both stack and heap allocated storage.
#[derive(Debug)]
pub enum BufferStorage<'a, const N: usize> {
    StackOwned(heapless::Vec<u8, N>),
    #[cfg(feature = "alloc")]
    HeapOwned(alloc::vec::Vec<u8>),
    Borrowed(&'a mut [u8]),
}
impl<const N: usize> BufferStorage<'_, N> {
    pub fn stack_filled(val: u8) -> Self {
        let mut buf: heapless::Vec<u8, N> = Default::default();
        buf.resize(N, val).expect("fixed cap");
        Self::StackOwned(buf)
    }

    #[cfg(feature = "alloc")]
    pub fn heap_filled(val: u8) -> Self {
        let mut buf: alloc::vec::Vec<u8> = Default::default();
        buf.resize(N, val);
        Self::HeapOwned(buf)
    }
}

impl<const N: usize> core::ops::Deref for BufferStorage<'_, N> {
    type Target = [u8];

    fn deref(&self) -> &Self::Target {
        match self {
            Self::StackOwned(vec) => &vec[..],
            #[cfg(feature = "alloc")]
            Self::HeapOwned(vec) => &vec[..],
            Self::Borrowed(slice) => &*slice,
        }
    }
}

impl<const N: usize> core::ops::DerefMut for BufferStorage<'_, N> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        match self {
            Self::StackOwned(vec) => &mut vec[..],
            #[cfg(feature = "alloc")]
            Self::HeapOwned(vec) => &mut vec[..],
            Self::Borrowed(slice) => &mut *slice,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn buffer_test<const N: usize>() {
        dbg!(N);
        let storages = [
            BufferStorage::<N>::stack_filled(0u8),
            #[cfg(feature = "alloc")]
            BufferStorage::<N>::heap_filled(0u8),
        ];
        for storage in storages {
            let mut buffer = Buffer::from_storage(storage);

            assert_eq!(buffer.remaining_mut(), N);
            assert_eq!(buffer.remaining(), 0);

            let source = [1u8; N];
            let chunk = buffer.chunk_mut();
            chunk[..N / 2].copy_from_slice(&source[..N / 2]);
            buffer.advance_mut(N / 2);

            assert_eq!(buffer.remaining_mut(), N / 2);
            assert_eq!(buffer.remaining(), N / 2);

            let chunk = buffer.chunk();
            assert_eq!(chunk.len(), N / 2);
            assert_eq!(chunk, &source[..N / 2]);

            buffer.advance(N / 4);
            assert_eq!(buffer.remaining(), N / 4);
            let chunk = buffer.chunk();
            assert_eq!(chunk.len(), N / 4);
            assert_eq!(chunk, &source[N / 4..N / 2]);

            buffer.advance(N / 4);
            assert_eq!(buffer.remaining(), 0);
            let chunk = buffer.chunk();
            assert_eq!(chunk.len(), 0);

            // write over the end
            let chunk = buffer.chunk_mut();
            assert_eq!(chunk.len(), N / 2);
            chunk.copy_from_slice(&source[..N / 2]);
            buffer.advance_mut(N / 2);
            assert_eq!(buffer.remaining_mut(), N / 2);
            assert_eq!(buffer.remaining(), N / 2);

            let chunk = buffer.chunk_mut();
            assert_eq!(chunk.len(), N / 2);
            chunk[..N / 4].copy_from_slice(&source[..N / 4]);
            buffer.advance_mut(N / 4);
            assert_eq!(buffer.remaining_mut(), N / 2 - N / 4);
            assert_eq!(buffer.remaining(), N / 2 + N / 4);
        }
    }

    #[test]
    fn test_buffer_basics() {
        // TODO: 1 and 2 size

        buffer_test::<4>();
        buffer_test::<8>();
        buffer_test::<16>();
        buffer_test::<64>();
        buffer_test::<128>();
        buffer_test::<256>();
        buffer_test::<512>();
        buffer_test::<1000>();
        buffer_test::<1024>();
    }
}
