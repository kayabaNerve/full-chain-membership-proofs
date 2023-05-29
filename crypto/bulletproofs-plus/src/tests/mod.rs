use rand_core::OsRng;

use ciphersuite::{group::Group, Ciphersuite, Pallas, Vesta};

use crate::{PointVector, gadgets::elliptic_curve::EmbeddedShortWeierstrass};

mod weighted_inner_product;
mod single_range_proof;
mod aggregate_range_proof;
mod arithmetic_circuit_proof;
mod arithmetic_circuit;
mod gadgets;

pub type Generators<C> = (
  <C as Ciphersuite>::G,
  <C as Ciphersuite>::G,
  PointVector<C>,
  PointVector<C>,
  PointVector<C>,
  PointVector<C>,
);

pub fn generators<C: Ciphersuite>(n: usize) -> Generators<C> {
  let gens = || {
    let mut res = PointVector::<C>::new(n);
    for i in 0 .. n {
      res[i] = C::G::random(&mut OsRng);
    }
    res
  };
  (C::G::random(&mut OsRng), C::G::random(&mut OsRng), gens(), gens(), gens(), gens())
}

impl EmbeddedShortWeierstrass for Pallas {
  type Embedded = Vesta;
  const B: u64 = 5;
}

impl EmbeddedShortWeierstrass for Vesta {
  type Embedded = Pallas;
  const B: u64 = 5;
}
