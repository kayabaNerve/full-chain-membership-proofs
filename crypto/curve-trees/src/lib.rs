#![allow(non_snake_case)]

use ciphersuite::Ciphersuite;

use ecip::Ecip;

pub mod pedersen_hash;
pub mod tree;

#[cfg(test)]
pub mod tests;

pub trait CurveCycle: Clone + Copy + PartialEq + Eq + core::fmt::Debug {
  type C1: Ecip;
  type C2: Ecip;

  fn c1_coords(
    point: <Self::C1 as Ciphersuite>::G,
  ) -> (<Self::C2 as Ciphersuite>::F, <Self::C2 as Ciphersuite>::F);
  fn c2_coords(
    point: <Self::C2 as Ciphersuite>::G,
  ) -> (<Self::C1 as Ciphersuite>::F, <Self::C1 as Ciphersuite>::F);
}
