use ciphersuite::{Ciphersuite, Ristretto, Pallas, Vesta};

use crate::{BulletproofsCurve, gadgets::elliptic_curve::EmbeddedShortWeierstrass};

mod weighted_inner_product;
mod single_range_proof;
mod aggregate_range_proof;
mod arithmetic_circuit_proof;
mod arithmetic_circuit;
mod gadgets;

impl BulletproofsCurve for Ristretto {
  fn alt_generator() -> <Self as Ciphersuite>::G {
    <Ristretto as Ciphersuite>::generator() *
      <Ristretto as Ciphersuite>::hash_to_F(b"alt_generator", &[]) // TODO
  }
}

impl BulletproofsCurve for Pallas {
  fn alt_generator() -> <Self as Ciphersuite>::G {
    <Pallas as Ciphersuite>::generator() * <Pallas as Ciphersuite>::hash_to_F(b"alt_generator", &[])
    // TODO
  }
}

impl BulletproofsCurve for Vesta {
  fn alt_generator() -> <Self as Ciphersuite>::G {
    <Vesta as Ciphersuite>::generator() * <Vesta as Ciphersuite>::hash_to_F(b"alt_generator", &[])
    // TODO
  }
}

impl EmbeddedShortWeierstrass for Pallas {
  const B: u64 = 5;
}

impl EmbeddedShortWeierstrass for Vesta {
  const B: u64 = 5;
}
