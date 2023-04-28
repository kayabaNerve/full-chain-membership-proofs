#![cfg_attr(docsrs, feature(doc_auto_cfg))]
#![doc = include_str!("../README.md")]
//#![no_std]

#[macro_use]
mod backend;

mod smaller;
pub use smaller::SmallerElement;

mod larger;
pub use larger::LargerElement;

mod point;
pub use point::{AlphaPoint, BetaPoint};
