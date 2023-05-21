#![allow(non_snake_case)]

use ciphersuite::Ciphersuite;

pub mod pedersen_hash;
pub mod tree;

pub trait CurveCycle: Clone + Copy + PartialEq + Eq {
  type C1: Ciphersuite;
  type C2: Ciphersuite;

  fn c1_coords(
    point: <Self::C1 as Ciphersuite>::G,
  ) -> (<Self::C2 as Ciphersuite>::F, <Self::C2 as Ciphersuite>::F);
  fn c2_coords(
    point: <Self::C2 as Ciphersuite>::G,
  ) -> (<Self::C1 as Ciphersuite>::F, <Self::C1 as Ciphersuite>::F);
}
