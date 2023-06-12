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
  let mut res = Generators::new(
    C::G::random(&mut OsRng),
    C::G::random(&mut OsRng),
    gens(),
    gens(),
    gens(),
    gens(),
  );

  // These use 2 * n since they're for the underlying g_bold, the concat of g_bold1, g_bold2
  let proving_gens = || {
    let mut res = Vec::with_capacity(2 * n);
    for _ in 0 .. (2 * n) {
      res.push(C::G::random(&mut OsRng));
    }
    res
  };
  res.add_vector_commitment_proving_generators(
    (C::G::random(&mut OsRng), C::G::random(&mut OsRng)),
    (proving_gens(), proving_gens()),
  );
  res
}

impl EmbeddedShortWeierstrass for Pallas {
  type Embedded = Vesta;
  const B: u64 = 5;
}

impl EmbeddedShortWeierstrass for Vesta {
  type Embedded = Pallas;
  const B: u64 = 5;
}
