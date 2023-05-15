use ciphersuite::{Ciphersuite, Ristretto};

use crate::BulletproofsCurve;

mod weighted_inner_product;
mod single_range_proof;
mod aggregate_range_proof;
mod arithmetic_circuit_proof;

impl BulletproofsCurve for Ristretto {
  fn alt_generator() -> <Self as Ciphersuite>::G {
    <Ristretto as Ciphersuite>::generator() *
      <Ristretto as Ciphersuite>::hash_to_F(b"alt_generator", &[]) // TODO
  }
  fn alt_generators() -> &'static [<Self as Ciphersuite>::G] {
    todo!()
  }
}
