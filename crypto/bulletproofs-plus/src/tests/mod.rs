use rand_core::OsRng;

use transcript::RecommendedTranscript;
use ciphersuite::{group::Group, Ciphersuite, Pallas, Vesta};

use crate::{Generators, padded_pow_of_2, gadgets::elliptic_curve::EmbeddedShortWeierstrass};

#[cfg(test)]
mod inner_product;

#[cfg(test)]
mod arithmetic_circuit_proof;

#[cfg(test)]
mod arithmetic_circuit;
#[cfg(test)]
mod gadgets;

pub fn generators<C: Ciphersuite>(n: usize) -> Generators<RecommendedTranscript, C> {
  assert_eq!(padded_pow_of_2(n), n, "amount of generators wasn't a power of 2");

  let gens = || {
    let mut res = Vec::with_capacity(n);
    for _ in 0 .. n {
      res.push(C::G::random(&mut OsRng));
    }
    res
  };
  Generators::new(C::G::random(&mut OsRng), C::G::random(&mut OsRng), gens(), gens())
}

impl EmbeddedShortWeierstrass for Pallas {
  type Embedded = Vesta;
  const B: u64 = 5;
}

impl EmbeddedShortWeierstrass for Vesta {
  type Embedded = Pallas;
  const B: u64 = 5;
}
