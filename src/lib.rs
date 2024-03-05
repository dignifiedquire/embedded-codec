#![allow(async_fn_in_trait)]
#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(feature = "alloc")]
extern crate alloc;

mod decoder;
mod encoder;
mod framed;
mod sink;
mod stream;

pub mod codecs;

// pub use self::buffer::Buffer;
pub use self::decoder::Decoder;
pub use self::encoder::Encoder;
pub use self::framed::{Framed, FramedRead, FramedWrite};
pub use self::sink::Sink;
pub use self::stream::Stream;
