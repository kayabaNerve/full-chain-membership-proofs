#![allow(non_snake_case)]

use zeroize::{Zeroize, ZeroizeOnDrop};

use ciphersuite::{group::ff::Field, Ciphersuite};

mod scalar_vector;
pub(crate) use scalar_vector::{ScalarVector, weighted_inner_product};
mod scalar_matrix;
pub(crate) use scalar_matrix::ScalarMatrix;
mod point_vector;
pub(crate) use point_vector::PointVector;

pub mod weighted_inner_product;
pub mod single_range_proof;
pub mod aggregate_range_proof;
pub mod arithmetic_circuit_proof;

#[cfg(test)]
mod tests;

pub const RANGE_PROOF_BITS: usize = 64;

pub trait BulletproofsCurve: Ciphersuite {
  fn alt_generator() -> <Self as Ciphersuite>::G;
  fn alt_generators() -> &'static [<Self as Ciphersuite>::G];
}

#[allow(non_snake_case)]
#[derive(Clone, PartialEq, Eq, Debug, Zeroize, ZeroizeOnDrop)]
pub struct Commitment<C: Ciphersuite> {
  pub value: u64,
  pub mask: C::F,
}

impl<C: BulletproofsCurve> Commitment<C> {
  pub fn zero() -> Self {
    Commitment { value: 0, mask: C::F::ZERO }
  }

  pub fn new(value: u64, mask: C::F) -> Self {
    Commitment { value, mask }
  }

  /// Calculate a Pedersen commitment, as a point, from the transparent structure.
  pub fn calculate(&self) -> C::G {
    (C::generator() * C::F::from(self.value)) + (C::alt_generator() * self.mask)
  }
}

// Returns the little-endian decomposition.
fn u64_decompose<C: BulletproofsCurve>(value: u64) -> ScalarVector<C> {
  let mut bits = ScalarVector::<C>::new(64);
  for bit in 0 .. 64 {
    bits[bit] = C::F::from((value & (1u64 << bit)) >> bit);
  }
  bits
}
