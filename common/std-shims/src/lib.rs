#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(not(feature = "std"))]
#[allow(unused_imports)]
#[doc(hidden)]
#[macro_use]
pub extern crate alloc;

pub mod collections;
pub mod io;

pub mod str {
  #[cfg(not(feature = "std"))]
  pub use alloc::str::*;
  #[cfg(feature = "std")]
  pub use std::str::*;
}

pub mod vec {
  #[cfg(not(feature = "std"))]
  pub use alloc::vec::*;
  #[cfg(feature = "std")]
  pub use std::vec::*;
}
