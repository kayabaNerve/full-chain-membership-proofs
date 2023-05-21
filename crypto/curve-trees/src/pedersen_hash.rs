use zeroize::Zeroize;

use rand_core::{RngCore, CryptoRng};

use transcript::Transcript;

use multiexp::{multiexp, multiexp_vartime};
use ciphersuite::{
  group::{ff::Field, Group, GroupEncoding},
  Ciphersuite,
};

use bulletproofs_plus::{
  ScalarVector, PointVector,
  weighted_inner_product::{WipStatement, WipWitness, WipProof},
};

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

/// Proves there's a known preimage for a blinded Pedersen hash.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct PedersenHashStatement<C: Ciphersuite> {
  generators: PointVector<C>,
  h: C::G,

  blinded_hash: C::G,
}
#[derive(Clone, PartialEq, Eq, Debug, Zeroize)]
pub struct PedersenHashWitness<C: Ciphersuite> {
  words: ScalarVector<C>,
  blind: C::F,
}
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct PedersenHashProof<C: Ciphersuite>(WipProof<C>);

impl<C: Ciphersuite> PedersenHashStatement<C> {
  pub fn new(generators: PointVector<C>, h: C::G, blinded_hash: C::G) -> Self {
    PedersenHashStatement { generators, h, blinded_hash }
  }

  fn transcript_hash<T: Transcript>(transcript: &mut T, blinded_hash: C::G) -> C::F {
    transcript.append_message(b"blinded_hash", blinded_hash.to_bytes());

    let y = C::hash_to_F(b"pedersen_hash_proof", transcript.challenge(b"y").as_ref());
    if bool::from(y.is_zero()) {
      panic!("zero challenge in pedersen hash proof");
    }
    y
  }

  pub fn prove<R: RngCore + CryptoRng, T: Transcript>(
    self,
    rng: &mut R,
    transcript: &mut T,
    witness: PedersenHashWitness<C>,
  ) -> PedersenHashProof<C> {
    assert_eq!(
      pedersen_hash::<C>(&witness.words.0, &self.generators.0) + (self.h * witness.blind),
      self.blinded_hash
    );

    let (left_gens, right_gens) = self.generators.split();
    let (left_words, right_words) = witness.words.split();

    let y = Self::transcript_hash(transcript, self.blinded_hash);
    PedersenHashProof(
      WipStatement::new(C::G::identity(), self.h, left_gens, right_gens, self.blinded_hash).prove(
        rng,
        transcript,
        WipWitness::new(left_words, right_words, witness.blind),
        y,
      ),
    )
  }

  pub fn verify<T: Transcript>(self, transcript: &mut T, proof: PedersenHashProof<C>) {
    let y = Self::transcript_hash(transcript, self.blinded_hash);
    let (left_gens, right_gens) = self.generators.split();
    (WipStatement::new(C::G::identity(), self.h, left_gens, right_gens, self.blinded_hash))
      .verify(transcript, proof.0, y);
  }
}
