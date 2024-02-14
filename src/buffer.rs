use core::{cmp, mem, ptr};

#[derive(Debug)]
pub struct Buffer<'a, const N: usize> {
    storage: BufferStorage<'a, N>,
    start: usize,
    end: usize,
}

macro_rules! buf_get_impl {
    ($this:ident, $typ:tt::$conv:tt) => {{
        const SIZE: usize = mem::size_of::<$typ>();
        // try to convert directly from the bytes
        // this Option<ret> trick is to avoid keeping a borrow on self
        // when advance() is called (mut borrow) and to call bytes() only once
        let ret = $this
            .chunk()
            .get(..SIZE)
            .map(|src| unsafe { $typ::$conv(*(src as *const _ as *const [_; SIZE])) });

        if let Some(ret) = ret {
            // if the direct conversion was possible, advance and return
            $this.advance(SIZE);
            return ret;
        } else {
            // if not we copy the bytes in a temp buffer then convert
            let mut buf = [0; SIZE];
            $this.copy_to_slice(&mut buf); // (do the advance)
            return $typ::$conv(buf);
        }
    }};
    (le => $this:ident, $typ:tt, $len_to_read:expr) => {{
        debug_assert!(mem::size_of::<$typ>() >= $len_to_read);

        // The same trick as above does not improve the best case speed.
        // It seems to be linked to the way the method is optimised by the compiler
        let mut buf = [0; (mem::size_of::<$typ>())];
        $this.copy_to_slice(&mut buf[..($len_to_read)]);
        return $typ::from_le_bytes(buf);
    }};
    (be => $this:ident, $typ:tt, $len_to_read:expr) => {{
        debug_assert!(mem::size_of::<$typ>() >= $len_to_read);

        let mut buf = [0; (mem::size_of::<$typ>())];
        $this.copy_to_slice(&mut buf[mem::size_of::<$typ>() - ($len_to_read)..]);
        return $typ::from_be_bytes(buf);
    }};
}

impl<'a, const N: usize> From<&'a mut [u8]> for Buffer<'a, N> {
    fn from(value: &'a mut [u8]) -> Self {
        Buffer::from_storage(BufferStorage::<N>::Borrowed(value))
    }
}

impl<'a, const N: usize> From<&'a [u8]> for Buffer<'a, N> {
    fn from(value: &'a [u8]) -> Self {
        let mut buffer = Buffer::<N>::new_stack();
        buffer.put_slice(value);
        buffer
    }
}

impl<'a, const N: usize> Buffer<'a, N> {
    /// A freshly initalized buffer on the stack.
    pub fn new_stack() -> Self {
        let storage = BufferStorage::<N>::stack_filled(0u8);
        Self::from_storage(storage)
    }

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

    pub fn has_remaining(&self) -> bool {
        self.remaining() > 0
    }

    pub fn len(&self) -> usize {
        self.remaining()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
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

    /// Returns an error if this much data is not available to write.
    pub fn ensure_capacity_mut(&self, cap: usize) -> Result<(), ()> {
        if self.remaining_mut() < cap {
            return Err(());
        }

        Ok(())
    }

    /// Transfer bytes into `self` from `src` and advance the cursor by the
    /// number of bytes written.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_codec::Buffer;
    ///
    /// let mut buf = Buffer::<64>::new_stack();
    /// let mut other = Buffer::<24>::new_stack();
    ///
    /// other.put_u8(b'h');
    /// other.put_slice(&b"ello"[..]);
    /// other.put_slice(&b" world"[..]);
    /// buf.put(&mut other);
    ///
    /// assert_eq!(buf.chunk(), b"hello world");
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if `self` does not have enough capacity to contain `src`.
    pub fn put<const M: usize>(&mut self, src: &mut Buffer<'_, M>)
    where
        Self: Sized,
    {
        assert!(self.remaining_mut() >= src.remaining());

        while src.has_remaining() {
            let l;

            unsafe {
                let s = src.chunk();
                let d = self.chunk_mut();
                l = cmp::min(s.len(), d.len());

                ptr::copy_nonoverlapping(s.as_ptr(), d.as_mut_ptr() as *mut u8, l);
            }

            src.advance(l);
            self.advance_mut(l);
        }
    }

    /// Transfer bytes into `self` from `src` and advance the cursor by the
    /// number of bytes written.
    ///
    /// `self` must have enough remaining capacity to contain all of `src`.
    ///
    /// ```
    /// use embedded_codec::Buffer;
    ///
    /// let mut buf = Buffer::<6>::new_stack();
    ///
    /// buf.put_slice(b"hello");
    /// assert_eq!(1, buf.remaining_mut());
    /// assert_eq!(b"hello", buf.chunk());
    /// ```
    pub fn put_slice(&mut self, src: &[u8]) {
        let mut off = 0;

        assert!(
            self.remaining_mut() >= src.len(),
            "buffer overflow; remaining = {}; src = {}",
            self.remaining_mut(),
            src.len()
        );

        while off < src.len() {
            let cnt;

            unsafe {
                let dst = self.chunk_mut();
                cnt = cmp::min(dst.len(), src.len() - off);

                ptr::copy_nonoverlapping(src[off..].as_ptr(), dst.as_mut_ptr() as *mut u8, cnt);

                off += cnt;
            }
            self.advance_mut(cnt);
        }
    }

    /// Put `cnt` bytes `val` into `self`.
    ///
    /// Logically equivalent to calling `self.put_u8(val)` `cnt` times, but may work faster.
    ///
    /// `self` must have at least `cnt` remaining capacity.
    ///
    /// ```
    /// use embedded_codec::Buffer;
    ///
    /// let mut buf = Buffer::<6>::new_stack();
    ///
    /// buf.put_bytes(b'a', 4);
    /// assert_eq!(2, buf.remaining_mut());
    /// assert_eq!(b"aaaa", buf.chunk());
    /// ```
    ///
    /// # Panics
    ///
    /// This function panics if there is not enough remaining capacity in
    /// `self`.
    pub fn put_bytes(&mut self, val: u8, cnt: usize) {
        for _ in 0..cnt {
            self.put_u8(val);
        }
    }

    /// Writes an unsigned 8 bit integer to `self`.
    ///
    /// The current position is advanced by 1.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_codec::Buffer;
    ///
    /// let mut buf = Buffer::<64>::new_stack();
    /// buf.put_u8(0x01);
    /// assert_eq!(buf.chunk(), b"\x01");
    /// ```
    ///
    /// # Panics
    ///
    /// This function panics if there is not enough remaining capacity in
    /// `self`.
    pub fn put_u8(&mut self, n: u8) {
        let src = [n];
        self.put_slice(&src);
    }

    /// Writes a signed 8 bit integer to `self`.
    ///
    /// The current position is advanced by 1.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_codec::Buffer;
    ///
    /// let mut buf = Buffer::<64>::new_stack();
    /// buf.put_i8(0x01);
    /// assert_eq!(buf.chunk(), b"\x01");
    /// ```
    ///
    /// # Panics
    ///
    /// This function panics if there is not enough remaining capacity in
    /// `self`.
    pub fn put_i8(&mut self, n: i8) {
        let src = [n as u8];
        self.put_slice(&src)
    }

    /// Writes an unsigned 16 bit integer to `self` in big-endian byte order.
    ///
    /// The current position is advanced by 2.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_codec::Buffer;
    ///
    /// let mut buf = Buffer::<64>::new_stack();
    /// buf.put_u16(0x0809);
    /// assert_eq!(buf.chunk(), b"\x08\x09");
    /// ```
    ///
    /// # Panics
    ///
    /// This function panics if there is not enough remaining capacity in
    /// `self`.
    pub fn put_u16(&mut self, n: u16) {
        self.put_slice(&n.to_be_bytes())
    }

    /// Writes an unsigned 16 bit integer to `self` in little-endian byte order.
    ///
    /// The current position is advanced by 2.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_codec::Buffer;
    ///
    /// let mut buf = Buffer::<64>::new_stack();
    /// buf.put_u16_le(0x0809);
    /// assert_eq!(buf.chunk(), b"\x09\x08");
    /// ```
    ///
    /// # Panics
    ///
    /// This function panics if there is not enough remaining capacity in
    /// `self`.
    pub fn put_u16_le(&mut self, n: u16) {
        self.put_slice(&n.to_le_bytes())
    }

    /// Writes an unsigned 16 bit integer to `self` in native-endian byte order.
    ///
    /// The current position is advanced by 2.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_codec::Buffer;
    ///
    /// let mut buf = Buffer::<64>::new_stack();
    /// buf.put_u16_ne(0x0809);
    /// if cfg!(target_endian = "big") {
    ///     assert_eq!(buf.chunk(), b"\x08\x09");
    /// } else {
    ///     assert_eq!(buf.chunk(), b"\x09\x08");
    /// }
    /// ```
    ///
    /// # Panics
    ///
    /// This function panics if there is not enough remaining capacity in
    /// `self`.
    pub fn put_u16_ne(&mut self, n: u16) {
        self.put_slice(&n.to_ne_bytes())
    }

    /// Writes a signed 16 bit integer to `self` in big-endian byte order.
    ///
    /// The current position is advanced by 2.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_codec::Buffer;
    ///
    /// let mut buf = Buffer::<64>::new_stack();
    /// buf.put_i16(0x0809);
    /// assert_eq!(buf.chunk(), b"\x08\x09");
    /// ```
    ///
    /// # Panics
    ///
    /// This function panics if there is not enough remaining capacity in
    /// `self`.
    pub fn put_i16(&mut self, n: i16) {
        self.put_slice(&n.to_be_bytes())
    }

    /// Writes a signed 16 bit integer to `self` in little-endian byte order.
    ///
    /// The current position is advanced by 2.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_codec::Buffer;
    ///
    /// let mut buf = Buffer::<64>::new_stack();
    /// buf.put_i16_le(0x0809);
    /// assert_eq!(buf.chunk(), b"\x09\x08");
    /// ```
    ///
    /// # Panics
    ///
    /// This function panics if there is not enough remaining capacity in
    /// `self`.
    pub fn put_i16_le(&mut self, n: i16) {
        self.put_slice(&n.to_le_bytes())
    }

    /// Writes a signed 16 bit integer to `self` in native-endian byte order.
    ///
    /// The current position is advanced by 2.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_codec::Buffer;
    ///
    /// let mut buf = Buffer::<64>::new_stack();
    /// buf.put_i16_ne(0x0809);
    /// if cfg!(target_endian = "big") {
    ///     assert_eq!(buf.chunk(), b"\x08\x09");
    /// } else {
    ///     assert_eq!(buf.chunk(), b"\x09\x08");
    /// }
    /// ```
    ///
    /// # Panics
    ///
    /// This function panics if there is not enough remaining capacity in
    /// `self`.
    pub fn put_i16_ne(&mut self, n: i16) {
        self.put_slice(&n.to_ne_bytes())
    }

    /// Writes an unsigned 32 bit integer to `self` in big-endian byte order.
    ///
    /// The current position is advanced by 4.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_codec::Buffer;
    ///
    /// let mut buf = Buffer::<64>::new_stack();
    /// buf.put_u32(0x0809A0A1);
    /// assert_eq!(buf.chunk(), b"\x08\x09\xA0\xA1");
    /// ```
    ///
    /// # Panics
    ///
    /// This function panics if there is not enough remaining capacity in
    /// `self`.
    pub fn put_u32(&mut self, n: u32) {
        self.put_slice(&n.to_be_bytes())
    }

    /// Writes an unsigned 32 bit integer to `self` in little-endian byte order.
    ///
    /// The current position is advanced by 4.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_codec::Buffer;
    ///
    /// let mut buf = Buffer::<64>::new_stack();
    /// buf.put_u32_le(0x0809A0A1);
    /// assert_eq!(buf.chunk(), b"\xA1\xA0\x09\x08");
    /// ```
    ///
    /// # Panics
    ///
    /// This function panics if there is not enough remaining capacity in
    /// `self`.
    pub fn put_u32_le(&mut self, n: u32) {
        self.put_slice(&n.to_le_bytes())
    }

    /// Writes an unsigned 32 bit integer to `self` in native-endian byte order.
    ///
    /// The current position is advanced by 4.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_codec::Buffer;
    ///
    /// let mut buf = Buffer::<64>::new_stack();
    /// buf.put_u32_ne(0x0809A0A1);
    /// if cfg!(target_endian = "big") {
    ///     assert_eq!(buf.chunk(), b"\x08\x09\xA0\xA1");
    /// } else {
    ///     assert_eq!(buf.chunk(), b"\xA1\xA0\x09\x08");
    /// }
    /// ```
    ///
    /// # Panics
    ///
    /// This function panics if there is not enough remaining capacity in
    /// `self`.
    pub fn put_u32_ne(&mut self, n: u32) {
        self.put_slice(&n.to_ne_bytes())
    }

    /// Writes a signed 32 bit integer to `self` in big-endian byte order.
    ///
    /// The current position is advanced by 4.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_codec::Buffer;
    ///
    /// let mut buf = Buffer::<64>::new_stack();
    /// buf.put_i32(0x0809A0A1);
    /// assert_eq!(buf.chunk(), b"\x08\x09\xA0\xA1");
    /// ```
    ///
    /// # Panics
    ///
    /// This function panics if there is not enough remaining capacity in
    /// `self`.
    pub fn put_i32(&mut self, n: i32) {
        self.put_slice(&n.to_be_bytes())
    }

    /// Writes a signed 32 bit integer to `self` in little-endian byte order.
    ///
    /// The current position is advanced by 4.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_codec::Buffer;
    ///
    /// let mut buf = Buffer::<64>::new_stack();
    /// buf.put_i32_le(0x0809A0A1);
    /// assert_eq!(buf.chunk(), b"\xA1\xA0\x09\x08");
    /// ```
    ///
    /// # Panics
    ///
    /// This function panics if there is not enough remaining capacity in
    /// `self`.
    pub fn put_i32_le(&mut self, n: i32) {
        self.put_slice(&n.to_le_bytes())
    }

    /// Writes a signed 32 bit integer to `self` in native-endian byte order.
    ///
    /// The current position is advanced by 4.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_codec::Buffer;
    ///
    /// let mut buf = Buffer::<64>::new_stack();
    /// buf.put_i32_ne(0x0809A0A1);
    /// if cfg!(target_endian = "big") {
    ///     assert_eq!(buf.chunk(), b"\x08\x09\xA0\xA1");
    /// } else {
    ///     assert_eq!(buf.chunk(), b"\xA1\xA0\x09\x08");
    /// }
    /// ```
    ///
    /// # Panics
    ///
    /// This function panics if there is not enough remaining capacity in
    /// `self`.
    pub fn put_i32_ne(&mut self, n: i32) {
        self.put_slice(&n.to_ne_bytes())
    }

    /// Writes an unsigned 64 bit integer to `self` in the big-endian byte order.
    ///
    /// The current position is advanced by 8.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_codec::Buffer;
    ///
    /// let mut buf = Buffer::<64>::new_stack();
    /// buf.put_u64(0x0102030405060708);
    /// assert_eq!(buf.chunk(), b"\x01\x02\x03\x04\x05\x06\x07\x08");
    /// ```
    ///
    /// # Panics
    ///
    /// This function panics if there is not enough remaining capacity in
    /// `self`.
    pub fn put_u64(&mut self, n: u64) {
        self.put_slice(&n.to_be_bytes())
    }

    /// Writes an unsigned 64 bit integer to `self` in little-endian byte order.
    ///
    /// The current position is advanced by 8.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_codec::Buffer;
    ///
    /// let mut buf = Buffer::<64>::new_stack();
    /// buf.put_u64_le(0x0102030405060708);
    /// assert_eq!(buf.chunk(), b"\x08\x07\x06\x05\x04\x03\x02\x01");
    /// ```
    ///
    /// # Panics
    ///
    /// This function panics if there is not enough remaining capacity in
    /// `self`.
    pub fn put_u64_le(&mut self, n: u64) {
        self.put_slice(&n.to_le_bytes())
    }

    /// Writes an unsigned 64 bit integer to `self` in native-endian byte order.
    ///
    /// The current position is advanced by 8.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_codec::Buffer;
    ///
    /// let mut buf = Buffer::<64>::new_stack();
    /// buf.put_u64_ne(0x0102030405060708);
    /// if cfg!(target_endian = "big") {
    ///     assert_eq!(buf.chunk(), b"\x01\x02\x03\x04\x05\x06\x07\x08");
    /// } else {
    ///     assert_eq!(buf.chunk(), b"\x08\x07\x06\x05\x04\x03\x02\x01");
    /// }
    /// ```
    ///
    /// # Panics
    ///
    /// This function panics if there is not enough remaining capacity in
    /// `self`.
    pub fn put_u64_ne(&mut self, n: u64) {
        self.put_slice(&n.to_ne_bytes())
    }

    /// Writes a signed 64 bit integer to `self` in the big-endian byte order.
    ///
    /// The current position is advanced by 8.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_codec::Buffer;
    ///
    /// let mut buf = Buffer::<64>::new_stack();
    /// buf.put_i64(0x0102030405060708);
    /// assert_eq!(buf.chunk(), b"\x01\x02\x03\x04\x05\x06\x07\x08");
    /// ```
    ///
    /// # Panics
    ///
    /// This function panics if there is not enough remaining capacity in
    /// `self`.
    pub fn put_i64(&mut self, n: i64) {
        self.put_slice(&n.to_be_bytes())
    }

    /// Writes a signed 64 bit integer to `self` in little-endian byte order.
    ///
    /// The current position is advanced by 8.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_codec::Buffer;
    ///
    /// let mut buf = Buffer::<64>::new_stack();
    /// buf.put_i64_le(0x0102030405060708);
    /// assert_eq!(buf.chunk(), b"\x08\x07\x06\x05\x04\x03\x02\x01");
    /// ```
    ///
    /// # Panics
    ///
    /// This function panics if there is not enough remaining capacity in
    /// `self`.
    pub fn put_i64_le(&mut self, n: i64) {
        self.put_slice(&n.to_le_bytes())
    }

    /// Writes a signed 64 bit integer to `self` in native-endian byte order.
    ///
    /// The current position is advanced by 8.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_codec::Buffer;
    ///
    /// let mut buf = Buffer::<64>::new_stack();
    /// buf.put_i64_ne(0x0102030405060708);
    /// if cfg!(target_endian = "big") {
    ///     assert_eq!(buf.chunk(), b"\x01\x02\x03\x04\x05\x06\x07\x08");
    /// } else {
    ///     assert_eq!(buf.chunk(), b"\x08\x07\x06\x05\x04\x03\x02\x01");
    /// }
    /// ```
    ///
    /// # Panics
    ///
    /// This function panics if there is not enough remaining capacity in
    /// `self`.
    pub fn put_i64_ne(&mut self, n: i64) {
        self.put_slice(&n.to_ne_bytes())
    }

    /// Writes an unsigned 128 bit integer to `self` in the big-endian byte order.
    ///
    /// The current position is advanced by 16.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_codec::Buffer;
    ///
    /// let mut buf = Buffer::<64>::new_stack();
    /// buf.put_u128(0x01020304050607080910111213141516);
    /// assert_eq!(buf.chunk(), b"\x01\x02\x03\x04\x05\x06\x07\x08\x09\x10\x11\x12\x13\x14\x15\x16");
    /// ```
    ///
    /// # Panics
    ///
    /// This function panics if there is not enough remaining capacity in
    /// `self`.
    pub fn put_u128(&mut self, n: u128) {
        self.put_slice(&n.to_be_bytes())
    }

    /// Writes an unsigned 128 bit integer to `self` in little-endian byte order.
    ///
    /// The current position is advanced by 16.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_codec::Buffer;
    ///
    /// let mut buf = Buffer::<64>::new_stack();
    /// buf.put_u128_le(0x01020304050607080910111213141516);
    /// assert_eq!(buf.chunk(), b"\x16\x15\x14\x13\x12\x11\x10\x09\x08\x07\x06\x05\x04\x03\x02\x01");
    /// ```
    ///
    /// # Panics
    ///
    /// This function panics if there is not enough remaining capacity in
    /// `self`.
    pub fn put_u128_le(&mut self, n: u128) {
        self.put_slice(&n.to_le_bytes())
    }

    /// Writes an unsigned 128 bit integer to `self` in native-endian byte order.
    ///
    /// The current position is advanced by 16.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_codec::Buffer;
    ///
    /// let mut buf = Buffer::<64>::new_stack();
    /// buf.put_u128_ne(0x01020304050607080910111213141516);
    /// if cfg!(target_endian = "big") {
    ///     assert_eq!(buf.chunk(), b"\x01\x02\x03\x04\x05\x06\x07\x08\x09\x10\x11\x12\x13\x14\x15\x16");
    /// } else {
    ///     assert_eq!(buf.chunk(), b"\x16\x15\x14\x13\x12\x11\x10\x09\x08\x07\x06\x05\x04\x03\x02\x01");
    /// }
    /// ```
    ///
    /// # Panics
    ///
    /// This function panics if there is not enough remaining capacity in
    /// `self`.
    pub fn put_u128_ne(&mut self, n: u128) {
        self.put_slice(&n.to_ne_bytes())
    }

    /// Writes a signed 128 bit integer to `self` in the big-endian byte order.
    ///
    /// The current position is advanced by 16.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_codec::Buffer;
    ///
    /// let mut buf = Buffer::<64>::new_stack();
    /// buf.put_i128(0x01020304050607080910111213141516);
    /// assert_eq!(buf.chunk(), b"\x01\x02\x03\x04\x05\x06\x07\x08\x09\x10\x11\x12\x13\x14\x15\x16");
    /// ```
    ///
    /// # Panics
    ///
    /// This function panics if there is not enough remaining capacity in
    /// `self`.
    pub fn put_i128(&mut self, n: i128) {
        self.put_slice(&n.to_be_bytes())
    }

    /// Writes a signed 128 bit integer to `self` in little-endian byte order.
    ///
    /// The current position is advanced by 16.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_codec::Buffer;
    ///
    /// let mut buf = Buffer::<64>::new_stack();
    /// buf.put_i128_le(0x01020304050607080910111213141516);
    /// assert_eq!(buf.chunk(), b"\x16\x15\x14\x13\x12\x11\x10\x09\x08\x07\x06\x05\x04\x03\x02\x01");
    /// ```
    ///
    /// # Panics
    ///
    /// This function panics if there is not enough remaining capacity in
    /// `self`.
    pub fn put_i128_le(&mut self, n: i128) {
        self.put_slice(&n.to_le_bytes())
    }

    /// Writes a signed 128 bit integer to `self` in native-endian byte order.
    ///
    /// The current position is advanced by 16.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_codec::Buffer;
    ///
    /// let mut buf = Buffer::<64>::new_stack();
    /// buf.put_i128_ne(0x01020304050607080910111213141516);
    /// if cfg!(target_endian = "big") {
    ///     assert_eq!(buf.chunk(), b"\x01\x02\x03\x04\x05\x06\x07\x08\x09\x10\x11\x12\x13\x14\x15\x16");
    /// } else {
    ///     assert_eq!(buf.chunk(), b"\x16\x15\x14\x13\x12\x11\x10\x09\x08\x07\x06\x05\x04\x03\x02\x01");
    /// }
    /// ```
    ///
    /// # Panics
    ///
    /// This function panics if there is not enough remaining capacity in
    /// `self`.
    pub fn put_i128_ne(&mut self, n: i128) {
        self.put_slice(&n.to_ne_bytes())
    }

    /// Writes an unsigned n-byte integer to `self` in big-endian byte order.
    ///
    /// The current position is advanced by `nbytes`.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_codec::Buffer;
    ///
    /// let mut buf = Buffer::<64>::new_stack();
    /// buf.put_uint(0x010203, 3);
    /// assert_eq!(buf.chunk(), b"\x01\x02\x03");
    /// ```
    ///
    /// # Panics
    ///
    /// This function panics if there is not enough remaining capacity in
    /// `self`.
    pub fn put_uint(&mut self, n: u64, nbytes: usize) {
        self.put_slice(&n.to_be_bytes()[mem::size_of_val(&n) - nbytes..]);
    }

    /// Writes an unsigned n-byte integer to `self` in the little-endian byte order.
    ///
    /// The current position is advanced by `nbytes`.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_codec::Buffer;
    ///
    /// let mut buf = Buffer::<64>::new_stack();
    /// buf.put_uint_le(0x010203, 3);
    /// assert_eq!(buf.chunk(), b"\x03\x02\x01");
    /// ```
    ///
    /// # Panics
    ///
    /// This function panics if there is not enough remaining capacity in
    /// `self`.
    pub fn put_uint_le(&mut self, n: u64, nbytes: usize) {
        self.put_slice(&n.to_le_bytes()[0..nbytes]);
    }

    /// Writes an unsigned n-byte integer to `self` in the native-endian byte order.
    ///
    /// The current position is advanced by `nbytes`.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_codec::Buffer;
    ///
    /// let mut buf = Buffer::<64>::new_stack();
    /// buf.put_uint_ne(0x010203, 3);
    /// if cfg!(target_endian = "big") {
    ///     assert_eq!(buf.chunk(), b"\x01\x02\x03");
    /// } else {
    ///     assert_eq!(buf.chunk(), b"\x03\x02\x01");
    /// }
    /// ```
    ///
    /// # Panics
    ///
    /// This function panics if there is not enough remaining capacity in
    /// `self`.
    pub fn put_uint_ne(&mut self, n: u64, nbytes: usize) {
        if cfg!(target_endian = "big") {
            self.put_uint(n, nbytes)
        } else {
            self.put_uint_le(n, nbytes)
        }
    }

    /// Writes low `nbytes` of a signed integer to `self` in big-endian byte order.
    ///
    /// The current position is advanced by `nbytes`.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_codec::Buffer;
    ///
    /// let mut buf = Buffer::<64>::new_stack();
    /// buf.put_int(0x0504010203, 3);
    /// assert_eq!(buf.chunk(), b"\x01\x02\x03");
    /// ```
    ///
    /// # Panics
    ///
    /// This function panics if there is not enough remaining capacity in
    /// `self` or if `nbytes` is greater than 8.
    pub fn put_int(&mut self, n: i64, nbytes: usize) {
        self.put_slice(&n.to_be_bytes()[mem::size_of_val(&n) - nbytes..]);
    }

    /// Writes low `nbytes` of a signed integer to `self` in little-endian byte order.
    ///
    /// The current position is advanced by `nbytes`.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_codec::Buffer;
    ///
    /// let mut buf = Buffer::<64>::new_stack();
    /// buf.put_int_le(0x0504010203, 3);
    /// assert_eq!(buf.chunk(), b"\x03\x02\x01");
    /// ```
    ///
    /// # Panics
    ///
    /// This function panics if there is not enough remaining capacity in
    /// `self` or if `nbytes` is greater than 8.
    pub fn put_int_le(&mut self, n: i64, nbytes: usize) {
        self.put_slice(&n.to_le_bytes()[0..nbytes]);
    }

    /// Writes low `nbytes` of a signed integer to `self` in native-endian byte order.
    ///
    /// The current position is advanced by `nbytes`.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_codec::Buffer;
    ///
    /// let mut buf = Buffer::<64>::new_stack();
    /// buf.put_int_ne(0x010203, 3);
    /// if cfg!(target_endian = "big") {
    ///     assert_eq!(buf.chunk(), b"\x01\x02\x03");
    /// } else {
    ///     assert_eq!(buf.chunk(), b"\x03\x02\x01");
    /// }
    /// ```
    ///
    /// # Panics
    ///
    /// This function panics if there is not enough remaining capacity in
    /// `self` or if `nbytes` is greater than 8.
    pub fn put_int_ne(&mut self, n: i64, nbytes: usize) {
        if cfg!(target_endian = "big") {
            self.put_int(n, nbytes)
        } else {
            self.put_int_le(n, nbytes)
        }
    }

    /// Writes  an IEEE754 single-precision (4 bytes) floating point number to
    /// `self` in big-endian byte order.
    ///
    /// The current position is advanced by 4.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_codec::Buffer;
    ///
    /// let mut buf = Buffer::<64>::new_stack();
    /// buf.put_f32(1.2f32);
    /// assert_eq!(buf.chunk(), b"\x3F\x99\x99\x9A");
    /// ```
    ///
    /// # Panics
    ///
    /// This function panics if there is not enough remaining capacity in
    /// `self`.
    pub fn put_f32(&mut self, n: f32) {
        self.put_u32(n.to_bits());
    }

    /// Writes  an IEEE754 single-precision (4 bytes) floating point number to
    /// `self` in little-endian byte order.
    ///
    /// The current position is advanced by 4.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_codec::Buffer;
    ///
    /// let mut buf = Buffer::<64>::new_stack();
    /// buf.put_f32_le(1.2f32);
    /// assert_eq!(buf.chunk(), b"\x9A\x99\x99\x3F");
    /// ```
    ///
    /// # Panics
    ///
    /// This function panics if there is not enough remaining capacity in
    /// `self`.
    pub fn put_f32_le(&mut self, n: f32) {
        self.put_u32_le(n.to_bits());
    }

    /// Writes an IEEE754 single-precision (4 bytes) floating point number to
    /// `self` in native-endian byte order.
    ///
    /// The current position is advanced by 4.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_codec::Buffer;
    ///
    /// let mut buf = Buffer::<64>::new_stack();
    /// buf.put_f32_ne(1.2f32);
    /// if cfg!(target_endian = "big") {
    ///     assert_eq!(buf.chunk(), b"\x3F\x99\x99\x9A");
    /// } else {
    ///     assert_eq!(buf.chunk(), b"\x9A\x99\x99\x3F");
    /// }
    /// ```
    ///
    /// # Panics
    ///
    /// This function panics if there is not enough remaining capacity in
    /// `self`.
    pub fn put_f32_ne(&mut self, n: f32) {
        self.put_u32_ne(n.to_bits());
    }

    /// Writes  an IEEE754 double-precision (8 bytes) floating point number to
    /// `self` in big-endian byte order.
    ///
    /// The current position is advanced by 8.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_codec::Buffer;
    ///
    /// let mut buf = Buffer::<64>::new_stack();
    /// buf.put_f64(1.2f64);
    /// assert_eq!(buf.chunk(), b"\x3F\xF3\x33\x33\x33\x33\x33\x33");
    /// ```
    ///
    /// # Panics
    ///
    /// This function panics if there is not enough remaining capacity in
    /// `self`.
    pub fn put_f64(&mut self, n: f64) {
        self.put_u64(n.to_bits());
    }

    /// Writes  an IEEE754 double-precision (8 bytes) floating point number to
    /// `self` in little-endian byte order.
    ///
    /// The current position is advanced by 8.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_codec::Buffer;
    ///
    /// let mut buf = Buffer::<64>::new_stack();
    /// buf.put_f64_le(1.2f64);
    /// assert_eq!(buf.chunk(), b"\x33\x33\x33\x33\x33\x33\xF3\x3F");
    /// ```
    ///
    /// # Panics
    ///
    /// This function panics if there is not enough remaining capacity in
    /// `self`.
    pub fn put_f64_le(&mut self, n: f64) {
        self.put_u64_le(n.to_bits());
    }

    /// Writes  an IEEE754 double-precision (8 bytes) floating point number to
    /// `self` in native-endian byte order.
    ///
    /// The current position is advanced by 8.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_codec::Buffer;
    ///
    /// let mut buf = Buffer::<64>::new_stack();
    /// buf.put_f64_ne(1.2f64);
    /// if cfg!(target_endian = "big") {
    ///     assert_eq!(buf.chunk(), b"\x3F\xF3\x33\x33\x33\x33\x33\x33");
    /// } else {
    ///     assert_eq!(buf.chunk(), b"\x33\x33\x33\x33\x33\x33\xF3\x3F");
    /// }
    /// ```
    ///
    /// # Panics
    ///
    /// This function panics if there is not enough remaining capacity in
    /// `self`.
    pub fn put_f64_ne(&mut self, n: f64) {
        self.put_u64_ne(n.to_bits());
    }

    /// Copies bytes from `self` into `dst`.
    ///
    /// The cursor is advanced by the number of bytes copied. `self` must have
    /// enough remaining bytes to fill `dst`.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_codec::Buffer;
    ///
    /// let mut buf: Buffer::<64> = b"hello world"[..].into();
    /// let mut dst = [0; 5];
    ///
    /// buf.copy_to_slice(&mut dst);
    /// assert_eq!(&b"hello"[..], &dst);
    /// assert_eq!(6, buf.remaining());
    /// ```
    ///
    /// # Panics
    ///
    /// This function panics if `self.remaining() < dst.len()`
    pub fn copy_to_slice(&mut self, dst: &mut [u8]) {
        let mut off = 0;

        assert!(self.remaining() >= dst.len());

        while off < dst.len() {
            let cnt;

            unsafe {
                let src = self.chunk();
                cnt = cmp::min(src.len(), dst.len() - off);

                ptr::copy_nonoverlapping(src.as_ptr(), dst[off..].as_mut_ptr(), cnt);

                off += cnt;
            }

            self.advance(cnt);
        }
    }

    /// Gets an unsigned 8 bit integer from `self`.
    ///
    /// The current position is advanced by 1.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_codec::Buffer;
    ///
    /// let mut buf: Buffer::<64> = b"\x08 hello"[..].into();
    /// assert_eq!(8, buf.get_u8());
    /// ```
    ///
    /// # Panics
    ///
    /// This function panics if there is no more remaining data in `self`.
    pub fn get_u8(&mut self) -> u8 {
        assert!(self.remaining() >= 1);
        let ret = self.chunk()[0];
        self.advance(1);
        ret
    }

    /// Gets a signed 8 bit integer from `self`.
    ///
    /// The current position is advanced by 1.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_codec::Buffer;
    ///
    /// let mut buf: Buffer::<64> = b"\x08 hello"[..].into();
    /// assert_eq!(8, buf.get_i8());
    /// ```
    ///
    /// # Panics
    ///
    /// This function panics if there is no more remaining data in `self`.
    pub fn get_i8(&mut self) -> i8 {
        assert!(self.remaining() >= 1);
        let ret = self.chunk()[0] as i8;
        self.advance(1);
        ret
    }

    /// Gets an unsigned 16 bit integer from `self` in big-endian byte order.
    ///
    /// The current position is advanced by 2.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_codec::Buffer;
    ///
    /// let mut buf: Buffer::<64> = b"\x08\x09 hello"[..].into();
    /// assert_eq!(0x0809, buf.get_u16());
    /// ```
    ///
    /// # Panics
    ///
    /// This function panics if there is not enough remaining data in `self`.
    pub fn get_u16(&mut self) -> u16 {
        buf_get_impl!(self, u16::from_be_bytes);
    }

    /// Gets an unsigned 16 bit integer from `self` in little-endian byte order.
    ///
    /// The current position is advanced by 2.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_codec::Buffer;
    ///
    /// let mut buf: Buffer::<64> = b"\x09\x08 hello"[..].into();
    /// assert_eq!(0x0809, buf.get_u16_le());
    /// ```
    ///
    /// # Panics
    ///
    /// This function panics if there is not enough remaining data in `self`.
    pub fn get_u16_le(&mut self) -> u16 {
        buf_get_impl!(self, u16::from_le_bytes);
    }

    /// Gets an unsigned 16 bit integer from `self` in native-endian byte order.
    ///
    /// The current position is advanced by 2.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_codec::Buffer;
    ///
    /// let mut buf: Buffer::<64> = match cfg!(target_endian = "big") {
    ///     true => b"\x08\x09 hello"[..].into(),
    ///     false => b"\x09\x08 hello"[..].into(),
    /// };
    /// assert_eq!(0x0809, buf.get_u16_ne());
    /// ```
    ///
    /// # Panics
    ///
    /// This function panics if there is not enough remaining data in `self`.
    pub fn get_u16_ne(&mut self) -> u16 {
        buf_get_impl!(self, u16::from_ne_bytes);
    }

    /// Gets a signed 16 bit integer from `self` in big-endian byte order.
    ///
    /// The current position is advanced by 2.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_codec::Buffer;
    ///
    /// let mut buf: Buffer::<64> = b"\x08\x09 hello"[..].into();
    /// assert_eq!(0x0809, buf.get_i16());
    /// ```
    ///
    /// # Panics
    ///
    /// This function panics if there is not enough remaining data in `self`.
    pub fn get_i16(&mut self) -> i16 {
        buf_get_impl!(self, i16::from_be_bytes);
    }

    /// Gets a signed 16 bit integer from `self` in little-endian byte order.
    ///
    /// The current position is advanced by 2.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_codec::Buffer;
    ///
    /// let mut buf: Buffer::<64> = b"\x09\x08 hello"[..].into();
    /// assert_eq!(0x0809, buf.get_i16_le());
    /// ```
    ///
    /// # Panics
    ///
    /// This function panics if there is not enough remaining data in `self`.
    pub fn get_i16_le(&mut self) -> i16 {
        buf_get_impl!(self, i16::from_le_bytes);
    }

    /// Gets a signed 16 bit integer from `self` in native-endian byte order.
    ///
    /// The current position is advanced by 2.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_codec::Buffer;
    ///
    /// let mut buf: Buffer::<64> = match cfg!(target_endian = "big") {
    ///     true => b"\x08\x09 hello"[..].into(),
    ///     false => b"\x09\x08 hello"[..].into(),
    /// };
    /// assert_eq!(0x0809, buf.get_i16_ne());
    /// ```
    ///
    /// # Panics
    ///
    /// This function panics if there is not enough remaining data in `self`.
    pub fn get_i16_ne(&mut self) -> i16 {
        buf_get_impl!(self, i16::from_ne_bytes);
    }

    /// Gets an unsigned 32 bit integer from `self` in the big-endian byte order.
    ///
    /// The current position is advanced by 4.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_codec::Buffer;
    ///
    /// let mut buf: Buffer::<64> = b"\x08\x09\xA0\xA1 hello"[..].into();
    /// assert_eq!(0x0809A0A1, buf.get_u32());
    /// ```
    ///
    /// # Panics
    ///
    /// This function panics if there is not enough remaining data in `self`.
    pub fn get_u32(&mut self) -> u32 {
        buf_get_impl!(self, u32::from_be_bytes);
    }

    /// Gets an unsigned 32 bit integer from `self` in the little-endian byte order.
    ///
    /// The current position is advanced by 4.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_codec::Buffer;
    ///
    /// let mut buf: Buffer::<64> = b"\xA1\xA0\x09\x08 hello"[..].into();
    /// assert_eq!(0x0809A0A1, buf.get_u32_le());
    /// ```
    ///
    /// # Panics
    ///
    /// This function panics if there is not enough remaining data in `self`.
    pub fn get_u32_le(&mut self) -> u32 {
        buf_get_impl!(self, u32::from_le_bytes);
    }

    /// Gets an unsigned 32 bit integer from `self` in native-endian byte order.
    ///
    /// The current position is advanced by 4.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_codec::Buffer;
    ///
    /// let mut buf: Buffer::<64> = match cfg!(target_endian = "big") {
    ///     true => b"\x08\x09\xA0\xA1 hello"[..].into(),
    ///     false => b"\xA1\xA0\x09\x08 hello"[..].into(),
    /// };
    /// assert_eq!(0x0809A0A1, buf.get_u32_ne());
    /// ```
    ///
    /// # Panics
    ///
    /// This function panics if there is not enough remaining data in `self`.
    pub fn get_u32_ne(&mut self) -> u32 {
        buf_get_impl!(self, u32::from_ne_bytes);
    }

    /// Gets a signed 32 bit integer from `self` in big-endian byte order.
    ///
    /// The current position is advanced by 4.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_codec::Buffer;
    ///
    /// let mut buf: Buffer::<64> = b"\x08\x09\xA0\xA1 hello"[..].into();
    /// assert_eq!(0x0809A0A1, buf.get_i32());
    /// ```
    ///
    /// # Panics
    ///
    /// This function panics if there is not enough remaining data in `self`.
    pub fn get_i32(&mut self) -> i32 {
        buf_get_impl!(self, i32::from_be_bytes);
    }

    /// Gets a signed 32 bit integer from `self` in little-endian byte order.
    ///
    /// The current position is advanced by 4.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_codec::Buffer;
    ///
    /// let mut buf: Buffer::<64> = b"\xA1\xA0\x09\x08 hello"[..].into();
    /// assert_eq!(0x0809A0A1, buf.get_i32_le());
    /// ```
    ///
    /// # Panics
    ///
    /// This function panics if there is not enough remaining data in `self`.
    pub fn get_i32_le(&mut self) -> i32 {
        buf_get_impl!(self, i32::from_le_bytes);
    }

    /// Gets a signed 32 bit integer from `self` in native-endian byte order.
    ///
    /// The current position is advanced by 4.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_codec::Buffer;
    ///
    /// let mut buf: Buffer::<64> = match cfg!(target_endian = "big") {
    ///     true => b"\x08\x09\xA0\xA1 hello"[..].into(),
    ///     false => b"\xA1\xA0\x09\x08 hello"[..].into(),
    /// };
    /// assert_eq!(0x0809A0A1, buf.get_i32_ne());
    /// ```
    ///
    /// # Panics
    ///
    /// This function panics if there is not enough remaining data in `self`.
    pub fn get_i32_ne(&mut self) -> i32 {
        buf_get_impl!(self, i32::from_ne_bytes);
    }

    /// Gets an unsigned 64 bit integer from `self` in big-endian byte order.
    ///
    /// The current position is advanced by 8.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_codec::Buffer;
    ///
    /// let mut buf: Buffer::<64> = b"\x01\x02\x03\x04\x05\x06\x07\x08 hello"[..].into();
    /// assert_eq!(0x0102030405060708, buf.get_u64());
    /// ```
    ///
    /// # Panics
    ///
    /// This function panics if there is not enough remaining data in `self`.
    pub fn get_u64(&mut self) -> u64 {
        buf_get_impl!(self, u64::from_be_bytes);
    }

    /// Gets an unsigned 64 bit integer from `self` in little-endian byte order.
    ///
    /// The current position is advanced by 8.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_codec::Buffer;
    ///
    /// let mut buf: Buffer::<64> = b"\x08\x07\x06\x05\x04\x03\x02\x01 hello"[..].into();
    /// assert_eq!(0x0102030405060708, buf.get_u64_le());
    /// ```
    ///
    /// # Panics
    ///
    /// This function panics if there is not enough remaining data in `self`.
    pub fn get_u64_le(&mut self) -> u64 {
        buf_get_impl!(self, u64::from_le_bytes);
    }

    /// Gets an unsigned 64 bit integer from `self` in native-endian byte order.
    ///
    /// The current position is advanced by 8.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_codec::Buffer;
    ///
    /// let mut buf: Buffer::<64> = match cfg!(target_endian = "big") {
    ///     true => b"\x01\x02\x03\x04\x05\x06\x07\x08 hello"[..].into(),
    ///     false => b"\x08\x07\x06\x05\x04\x03\x02\x01 hello"[..].into(),
    /// };
    /// assert_eq!(0x0102030405060708, buf.get_u64_ne());
    /// ```
    ///
    /// # Panics
    ///
    /// This function panics if there is not enough remaining data in `self`.
    pub fn get_u64_ne(&mut self) -> u64 {
        buf_get_impl!(self, u64::from_ne_bytes);
    }

    /// Gets a signed 64 bit integer from `self` in big-endian byte order.
    ///
    /// The current position is advanced by 8.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_codec::Buffer;
    ///
    /// let mut buf: Buffer::<64> = b"\x01\x02\x03\x04\x05\x06\x07\x08 hello"[..].into();
    /// assert_eq!(0x0102030405060708, buf.get_i64());
    /// ```
    ///
    /// # Panics
    ///
    /// This function panics if there is not enough remaining data in `self`.
    pub fn get_i64(&mut self) -> i64 {
        buf_get_impl!(self, i64::from_be_bytes);
    }

    /// Gets a signed 64 bit integer from `self` in little-endian byte order.
    ///
    /// The current position is advanced by 8.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_codec::Buffer;
    ///
    /// let mut buf: Buffer::<64> = b"\x08\x07\x06\x05\x04\x03\x02\x01 hello"[..].into();
    /// assert_eq!(0x0102030405060708, buf.get_i64_le());
    /// ```
    ///
    /// # Panics
    ///
    /// This function panics if there is not enough remaining data in `self`.
    pub fn get_i64_le(&mut self) -> i64 {
        buf_get_impl!(self, i64::from_le_bytes);
    }

    /// Gets a signed 64 bit integer from `self` in native-endian byte order.
    ///
    /// The current position is advanced by 8.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_codec::Buffer;
    ///
    /// let mut buf: Buffer::<64> = match cfg!(target_endian = "big") {
    ///     true => b"\x01\x02\x03\x04\x05\x06\x07\x08 hello"[..].into(),
    ///     false => b"\x08\x07\x06\x05\x04\x03\x02\x01 hello"[..].into(),
    /// };
    /// assert_eq!(0x0102030405060708, buf.get_i64_ne());
    /// ```
    ///
    /// # Panics
    ///
    /// This function panics if there is not enough remaining data in `self`.
    pub fn get_i64_ne(&mut self) -> i64 {
        buf_get_impl!(self, i64::from_ne_bytes);
    }

    /// Gets an unsigned 128 bit integer from `self` in big-endian byte order.
    ///
    /// The current position is advanced by 16.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_codec::Buffer;
    ///
    /// let mut buf: Buffer::<64> = b"\x01\x02\x03\x04\x05\x06\x07\x08\x09\x10\x11\x12\x13\x14\x15\x16 hello"[..].into();
    /// assert_eq!(0x01020304050607080910111213141516, buf.get_u128());
    /// ```
    ///
    /// # Panics
    ///
    /// This function panics if there is not enough remaining data in `self`.
    pub fn get_u128(&mut self) -> u128 {
        buf_get_impl!(self, u128::from_be_bytes);
    }

    /// Gets an unsigned 128 bit integer from `self` in little-endian byte order.
    ///
    /// The current position is advanced by 16.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_codec::Buffer;
    ///
    /// let mut buf: Buffer::<64> = b"\x16\x15\x14\x13\x12\x11\x10\x09\x08\x07\x06\x05\x04\x03\x02\x01 hello"[..].into();
    /// assert_eq!(0x01020304050607080910111213141516, buf.get_u128_le());
    /// ```
    ///
    /// # Panics
    ///
    /// This function panics if there is not enough remaining data in `self`.
    pub fn get_u128_le(&mut self) -> u128 {
        buf_get_impl!(self, u128::from_le_bytes);
    }

    /// Gets an unsigned 128 bit integer from `self` in native-endian byte order.
    ///
    /// The current position is advanced by 16.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_codec::Buffer;
    ///
    /// let mut buf: Buffer::<64> = match cfg!(target_endian = "big") {
    ///     true => b"\x01\x02\x03\x04\x05\x06\x07\x08\x09\x10\x11\x12\x13\x14\x15\x16 hello"[..].into(),
    ///     false => b"\x16\x15\x14\x13\x12\x11\x10\x09\x08\x07\x06\x05\x04\x03\x02\x01 hello"[..].into(),
    /// };
    /// assert_eq!(0x01020304050607080910111213141516, buf.get_u128_ne());
    /// ```
    ///
    /// # Panics
    ///
    /// This function panics if there is not enough remaining data in `self`.
    pub fn get_u128_ne(&mut self) -> u128 {
        buf_get_impl!(self, u128::from_ne_bytes);
    }

    /// Gets a signed 128 bit integer from `self` in big-endian byte order.
    ///
    /// The current position is advanced by 16.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_codec::Buffer;
    ///
    /// let mut buf: Buffer::<64> = b"\x01\x02\x03\x04\x05\x06\x07\x08\x09\x10\x11\x12\x13\x14\x15\x16 hello"[..].into();
    /// assert_eq!(0x01020304050607080910111213141516, buf.get_i128());
    /// ```
    ///
    /// # Panics
    ///
    /// This function panics if there is not enough remaining data in `self`.
    pub fn get_i128(&mut self) -> i128 {
        buf_get_impl!(self, i128::from_be_bytes);
    }

    /// Gets a signed 128 bit integer from `self` in little-endian byte order.
    ///
    /// The current position is advanced by 16.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_codec::Buffer;
    ///
    /// let mut buf: Buffer::<64> = b"\x16\x15\x14\x13\x12\x11\x10\x09\x08\x07\x06\x05\x04\x03\x02\x01 hello"[..].into();
    /// assert_eq!(0x01020304050607080910111213141516, buf.get_i128_le());
    /// ```
    ///
    /// # Panics
    ///
    /// This function panics if there is not enough remaining data in `self`.
    pub fn get_i128_le(&mut self) -> i128 {
        buf_get_impl!(self, i128::from_le_bytes);
    }

    /// Gets a signed 128 bit integer from `self` in native-endian byte order.
    ///
    /// The current position is advanced by 16.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_codec::Buffer;
    ///
    /// let mut buf: Buffer::<64> = match cfg!(target_endian = "big") {
    ///     true => b"\x01\x02\x03\x04\x05\x06\x07\x08\x09\x10\x11\x12\x13\x14\x15\x16 hello"[..].into(),
    ///     false => b"\x16\x15\x14\x13\x12\x11\x10\x09\x08\x07\x06\x05\x04\x03\x02\x01 hello"[..].into(),
    /// };
    /// assert_eq!(0x01020304050607080910111213141516, buf.get_i128_ne());
    /// ```
    ///
    /// # Panics
    ///
    /// This function panics if there is not enough remaining data in `self`.
    pub fn get_i128_ne(&mut self) -> i128 {
        buf_get_impl!(self, i128::from_ne_bytes);
    }

    /// Gets an unsigned n-byte integer from `self` in big-endian byte order.
    ///
    /// The current position is advanced by `nbytes`.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_codec::Buffer;
    ///
    /// let mut buf: Buffer::<64> = b"\x01\x02\x03 hello"[..].into();
    /// assert_eq!(0x010203, buf.get_uint(3));
    /// ```
    ///
    /// # Panics
    ///
    /// This function panics if there is not enough remaining data in `self`.
    pub fn get_uint(&mut self, nbytes: usize) -> u64 {
        buf_get_impl!(be => self, u64, nbytes);
    }

    /// Gets an unsigned n-byte integer from `self` in little-endian byte order.
    ///
    /// The current position is advanced by `nbytes`.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_codec::Buffer;
    ///
    /// let mut buf: Buffer::<64> = b"\x03\x02\x01 hello"[..].into();
    /// assert_eq!(0x010203, buf.get_uint_le(3));
    /// ```
    ///
    /// # Panics
    ///
    /// This function panics if there is not enough remaining data in `self`.
    pub fn get_uint_le(&mut self, nbytes: usize) -> u64 {
        buf_get_impl!(le => self, u64, nbytes);
    }

    /// Gets an unsigned n-byte integer from `self` in native-endian byte order.
    ///
    /// The current position is advanced by `nbytes`.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_codec::Buffer;
    ///
    /// let mut buf: Buffer::<64> = match cfg!(target_endian = "big") {
    ///     true => b"\x01\x02\x03 hello"[..].into(),
    ///     false => b"\x03\x02\x01 hello"[..].into(),
    /// };
    /// assert_eq!(0x010203, buf.get_uint_ne(3));
    /// ```
    ///
    /// # Panics
    ///
    /// This function panics if there is not enough remaining data in `self`.
    pub fn get_uint_ne(&mut self, nbytes: usize) -> u64 {
        if cfg!(target_endian = "big") {
            self.get_uint(nbytes)
        } else {
            self.get_uint_le(nbytes)
        }
    }

    /// Gets a signed n-byte integer from `self` in big-endian byte order.
    ///
    /// The current position is advanced by `nbytes`.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_codec::Buffer;
    ///
    /// let mut buf: Buffer::<64> = b"\x01\x02\x03 hello"[..].into();
    /// assert_eq!(0x010203, buf.get_int(3));
    /// ```
    ///
    /// # Panics
    ///
    /// This function panics if there is not enough remaining data in `self`.
    pub fn get_int(&mut self, nbytes: usize) -> i64 {
        buf_get_impl!(be => self, i64, nbytes);
    }

    /// Gets a signed n-byte integer from `self` in little-endian byte order.
    ///
    /// The current position is advanced by `nbytes`.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_codec::Buffer;
    ///
    /// let mut buf: Buffer::<64> = b"\x03\x02\x01 hello"[..].into();
    /// assert_eq!(0x010203, buf.get_int_le(3));
    /// ```
    ///
    /// # Panics
    ///
    /// This function panics if there is not enough remaining data in `self`.
    pub fn get_int_le(&mut self, nbytes: usize) -> i64 {
        buf_get_impl!(le => self, i64, nbytes);
    }

    /// Gets a signed n-byte integer from `self` in native-endian byte order.
    ///
    /// The current position is advanced by `nbytes`.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_codec::Buffer;
    ///
    /// let mut buf: Buffer::<64> = match cfg!(target_endian = "big") {
    ///     true => b"\x01\x02\x03 hello"[..].into(),
    ///     false => b"\x03\x02\x01 hello"[..].into(),
    /// };
    /// assert_eq!(0x010203, buf.get_int_ne(3));
    /// ```
    ///
    /// # Panics
    ///
    /// This function panics if there is not enough remaining data in `self`.
    pub fn get_int_ne(&mut self, nbytes: usize) -> i64 {
        if cfg!(target_endian = "big") {
            self.get_int(nbytes)
        } else {
            self.get_int_le(nbytes)
        }
    }

    /// Gets an IEEE754 single-precision (4 bytes) floating point number from
    /// `self` in big-endian byte order.
    ///
    /// The current position is advanced by 4.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_codec::Buffer;
    ///
    /// let mut buf: Buffer::<64> = b"\x3F\x99\x99\x9A hello"[..].into();
    /// assert_eq!(1.2f32, buf.get_f32());
    /// ```
    ///
    /// # Panics
    ///
    /// This function panics if there is not enough remaining data in `self`.
    pub fn get_f32(&mut self) -> f32 {
        f32::from_bits(Self::get_u32(self))
    }

    /// Gets an IEEE754 single-precision (4 bytes) floating point number from
    /// `self` in little-endian byte order.
    ///
    /// The current position is advanced by 4.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_codec::Buffer;
    ///
    /// let mut buf: Buffer::<64> = b"\x9A\x99\x99\x3F hello"[..].into();
    /// assert_eq!(1.2f32, buf.get_f32_le());
    /// ```
    ///
    /// # Panics
    ///
    /// This function panics if there is not enough remaining data in `self`.
    pub fn get_f32_le(&mut self) -> f32 {
        f32::from_bits(Self::get_u32_le(self))
    }

    /// Gets an IEEE754 single-precision (4 bytes) floating point number from
    /// `self` in native-endian byte order.
    ///
    /// The current position is advanced by 4.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_codec::Buffer;
    ///
    /// let mut buf: Buffer::<64> = match cfg!(target_endian = "big") {
    ///     true => b"\x3F\x99\x99\x9A hello"[..].into(),
    ///     false => b"\x9A\x99\x99\x3F hello"[..].into(),
    /// };
    /// assert_eq!(1.2f32, buf.get_f32_ne());
    /// ```
    ///
    /// # Panics
    ///
    /// This function panics if there is not enough remaining data in `self`.
    pub fn get_f32_ne(&mut self) -> f32 {
        f32::from_bits(Self::get_u32_ne(self))
    }

    /// Gets an IEEE754 double-precision (8 bytes) floating point number from
    /// `self` in big-endian byte order.
    ///
    /// The current position is advanced by 8.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_codec::Buffer;
    ///
    /// let mut buf: Buffer::<64> = b"\x3F\xF3\x33\x33\x33\x33\x33\x33 hello"[..].into();
    /// assert_eq!(1.2f64, buf.get_f64());
    /// ```
    ///
    /// # Panics
    ///
    /// This function panics if there is not enough remaining data in `self`.
    pub fn get_f64(&mut self) -> f64 {
        f64::from_bits(Self::get_u64(self))
    }

    /// Gets an IEEE754 double-precision (8 bytes) floating point number from
    /// `self` in little-endian byte order.
    ///
    /// The current position is advanced by 8.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_codec::Buffer;
    ///
    /// let mut buf: Buffer::<64> = b"\x33\x33\x33\x33\x33\x33\xF3\x3F hello"[..].into();
    /// assert_eq!(1.2f64, buf.get_f64_le());
    /// ```
    ///
    /// # Panics
    ///
    /// This function panics if there is not enough remaining data in `self`.
    pub fn get_f64_le(&mut self) -> f64 {
        f64::from_bits(Self::get_u64_le(self))
    }

    /// Gets an IEEE754 double-precision (8 bytes) floating point number from
    /// `self` in native-endian byte order.
    ///
    /// The current position is advanced by 8.
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_codec::Buffer;
    ///
    /// let mut buf: Buffer::<64> = match cfg!(target_endian = "big") {
    ///     true => b"\x3F\xF3\x33\x33\x33\x33\x33\x33 hello"[..].into(),
    ///     false => b"\x33\x33\x33\x33\x33\x33\xF3\x3F hello"[..].into(),
    /// };
    /// assert_eq!(1.2f64, buf.get_f64_ne());
    /// ```
    ///
    /// # Panics
    ///
    /// This function panics if there is not enough remaining data in `self`.
    pub fn get_f64_ne(&mut self) -> f64 {
        f64::from_bits(Self::get_u64_ne(self))
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
    pub fn stack() -> Self {
        let buf: heapless::Vec<u8, N> = Default::default();
        Self::StackOwned(buf)
    }

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
