use zeroize::Zeroize;

use multiexp::{multiexp, multiexp_vartime};

use ciphersuite::Ciphersuite;

pub fn pedersen_hash<C: Ciphersuite>(words: &[C::F], generators: &[C::G]) -> C::G {
  assert_eq!(words.len(), generators.len());
  let mut terms = words.iter().copied().zip(generators.iter().copied()).collect::<Vec<_>>();
  let res = multiexp(&terms);
  terms.zeroize();
  res
}

pub fn pedersen_hash_vartime<C: Ciphersuite>(words: &[C::F], generators: &[C::G]) -> C::G {
  assert_eq!(words.len(), generators.len());
  let mut terms = words.iter().copied().zip(generators.iter().copied()).collect::<Vec<_>>();
  let res = multiexp_vartime(&terms);
  terms.zeroize();
  res
}
