#![allow(non_snake_case)]

use ciphersuite::Ciphersuite;

pub enum Variable<C: Ciphersuite> {
  Prover(C::F),
  Verifier(),
}
