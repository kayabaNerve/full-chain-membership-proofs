use rand_core::OsRng;

use transcript::RecommendedTranscript;
use ciphersuite::{group::Group, Ciphersuite, Pallas, Vesta};

use crate::{Generators, gadgets::elliptic_curve::EmbeddedShortWeierstrass};

#[cfg(test)]
mod weighted_inner_product;
#[cfg(test)]
mod single_range_proof;
#[cfg(test)]
mod aggregate_range_proof;

#[cfg(test)]
mod arithmetic_circuit_proof;
#[cfg(test)]
mod arithmetic_circuit;
#[cfg(test)]
mod vector_commitment;
#[cfg(test)]
mod gadgets;

pub fn generators<C: Ciphersuite>(n: usize) -> Generators<RecommendedTranscript, C> {
  let gens = || {
    let mut res = Vec::with_capacity(n);
    for _ in 0 .. n {
      res.push(C::G::random(&mut OsRng));
    }
    res
  };
  Generators::new(
    C::G::random(&mut OsRng),
    C::G::random(&mut OsRng),
    gens(),
    gens(),
    gens(),
    gens(),
  )
}

impl EmbeddedShortWeierstrass for Pallas {
  type Embedded = Vesta;
  const B: u64 = 5;
}

impl EmbeddedShortWeierstrass for Vesta {
  type Embedded = Pallas;
  const B: u64 = 5;
}
