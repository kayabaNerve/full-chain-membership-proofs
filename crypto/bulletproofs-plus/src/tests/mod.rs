use rand_core::OsRng;

use ciphersuite::{group::Group, Ciphersuite, Ristretto, Pallas, Vesta};

use crate::{BulletproofsCurve, PointVector, gadgets::elliptic_curve::EmbeddedShortWeierstrass};

mod weighted_inner_product;
mod single_range_proof;
mod aggregate_range_proof;
mod arithmetic_circuit_proof;
mod arithmetic_circuit;
mod gadgets;

pub type Generators<C> = (PointVector<C>, PointVector<C>, PointVector<C>, PointVector<C>);

pub fn generators<C: BulletproofsCurve>(n: usize) -> Generators<C> {
  let gens = || {
    let mut res = PointVector::<C>::new(n);
    for i in 0 .. n {
      res[i] = C::G::random(&mut OsRng);
    }
    res
  };
  (gens(), gens(), gens(), gens())
}

// TODO: All of these suites use insecure alternate generators
// Even though they're only here for tests, they should still be proper

impl BulletproofsCurve for Ristretto {
  fn alt_generator() -> <Self as Ciphersuite>::G {
    <Ristretto as Ciphersuite>::generator() *
      <Ristretto as Ciphersuite>::hash_to_F(b"alt_generator", &[])
  }
}

impl BulletproofsCurve for Pallas {
  fn alt_generator() -> <Self as Ciphersuite>::G {
    <Pallas as Ciphersuite>::generator() * <Pallas as Ciphersuite>::hash_to_F(b"alt_generator", &[])
  }
}

impl BulletproofsCurve for Vesta {
  fn alt_generator() -> <Self as Ciphersuite>::G {
    <Vesta as Ciphersuite>::generator() * <Vesta as Ciphersuite>::hash_to_F(b"alt_generator", &[])
  }
}

impl EmbeddedShortWeierstrass for Pallas {
  const B: u64 = 5;
}

impl EmbeddedShortWeierstrass for Vesta {
  const B: u64 = 5;
}
