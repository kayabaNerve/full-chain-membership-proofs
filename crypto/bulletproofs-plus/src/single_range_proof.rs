use rand_core::{RngCore, CryptoRng};

use zeroize::{Zeroize, ZeroizeOnDrop};

use transcript::Transcript;

use multiexp::BatchVerifier;
use ciphersuite::{
  group::{ff::Field, GroupEncoding},
  Ciphersuite,
};

use crate::{
  RANGE_PROOF_BITS, ScalarVector, PointVector, Generators, RangeCommitment,
  weighted_inner_product::{WipStatement, WipWitness, WipProof},
  u64_decompose,
};

// Figure 2
#[derive(Clone, Debug, Zeroize)]
pub struct SingleRangeStatement<T: Transcript, C: Ciphersuite> {
  generators: Generators<T, C>,
  V: C::G,
}

#[derive(Clone, Debug, Zeroize, ZeroizeOnDrop)]
pub struct SingleRangeWitness<C: Ciphersuite> {
  value: u64,
  gamma: C::F,
}

impl<C: Ciphersuite> SingleRangeWitness<C> {
  pub fn new(commitment: RangeCommitment<C>) -> Self {
    SingleRangeWitness { value: commitment.value, gamma: commitment.mask }
  }
}

#[derive(Clone, Debug, Zeroize)]
pub struct SingleRangeProof<C: Ciphersuite> {
  A: C::G,
  wip: WipProof<C>,
}

impl<T: Transcript, C: Ciphersuite> SingleRangeStatement<T, C> {
  pub fn new(generators: Generators<T, C>, V: C::G) -> Self {
    Self { generators, V }
  }

  fn initial_transcript(&self, transcript: &mut T) {
    transcript.domain_separate(b"single_range_proof");
    transcript.append_message(b"commitment", self.V.to_bytes());
  }

  fn transcript_A(transcript: &mut T, A: C::G) -> (C::F, C::F) {
    transcript.append_message(b"A", A.to_bytes());

    let y = C::hash_to_F(b"single_range_proof", transcript.challenge(b"y").as_ref());
    if bool::from(y.is_zero()) {
      panic!("zero challenge in single range proof");
    }

    let z = C::hash_to_F(b"single_range_proof", transcript.challenge(b"z").as_ref());
    if bool::from(z.is_zero()) {
      panic!("zero challenge in single range proof");
    }

    (y, z)
  }

  fn A_hat(
    transcript: &mut T,
    g: C::G,
    g_bold: &PointVector<C>,
    h_bold: &PointVector<C>,
    V: C::G,
    A: C::G,
  ) -> (C::F, ScalarVector<C>, C::F, ScalarVector<C>, C::G) {
    assert_eq!(g_bold.len(), RANGE_PROOF_BITS);

    // TODO: First perform the WIP transcript before acquiring challenges
    let (y, z) = Self::transcript_A(transcript, A);

    let two_pows = ScalarVector::powers(C::F::from(2), RANGE_PROOF_BITS);
    // Collapse of [1; RANGE_PROOF_BITS] * z
    let z_vec = ScalarVector(vec![z; RANGE_PROOF_BITS]);

    let mut ascending_y = ScalarVector(vec![y]);
    for i in 1 .. RANGE_PROOF_BITS {
      ascending_y.0.push(ascending_y[i - 1] * y);
    }

    let mut descending_y = ascending_y.clone();
    descending_y.0.reverse();

    let y_n_plus_one = descending_y[0] * y;
    debug_assert_eq!(y_n_plus_one, y.pow([u64::try_from(RANGE_PROOF_BITS).unwrap() + 1]));
    let y_pows = ascending_y.sum();

    let two_descending_y = two_pows.mul_vec(&descending_y);
    (
      y,
      two_descending_y.clone(),
      y_n_plus_one,
      z_vec.clone(),
      A + g_bold.mul_vec(&ScalarVector(vec![-z; RANGE_PROOF_BITS])).sum() +
        h_bold.mul_vec(&two_descending_y.add_vec(&z_vec)).sum() +
        (V * y_n_plus_one) +
        (g * ((y_pows * z) - (two_pows.sum() * y_n_plus_one * z) - (y_pows * z.square()))),
    )
  }

  pub fn prove<R: RngCore + CryptoRng>(
    self,
    rng: &mut R,
    transcript: &mut T,
    witness: SingleRangeWitness<C>,
  ) -> SingleRangeProof<C> {
    self.initial_transcript(transcript);

    let Self { generators, V } = self;
    debug_assert_eq!(
      RangeCommitment::<C>::new(witness.value, witness.gamma)
        .calculate(generators.g(), generators.h()),
      V
    );

    let alpha = C::F::random(&mut *rng);
    let a_l = u64_decompose::<C>(witness.value);
    debug_assert_eq!(
      a_l.inner_product(&ScalarVector::powers(C::F::from(2), RANGE_PROOF_BITS)),
      C::F::from(witness.value),
    );
    let a_r = a_l.sub(C::F::ONE);
    debug_assert!(bool::from(a_l.inner_product(&a_r).is_zero()));

    let g_bold = generators.g_bold();
    let h_bold = generators.h_bold();
    let A = g_bold.mul_vec(&a_l).sum() + h_bold.mul_vec(&a_r).sum() + (generators.h() * alpha);
    let (y, two_descending_y, y_n_plus_one, z_vec, A_hat) =
      Self::A_hat(transcript, generators.g(), g_bold, h_bold, V, A);

    let a_l = a_l.sub_vec(&z_vec);
    let a_r = a_r.add_vec(&two_descending_y).add_vec(&z_vec);
    let alpha = alpha + (witness.gamma * y_n_plus_one);

    SingleRangeProof {
      A,
      wip: WipStatement::new(generators, A_hat, y).prove(
        rng,
        transcript,
        WipWitness::new(a_l, a_r, alpha),
      ),
    }
  }

  pub fn verify<R: RngCore + CryptoRng>(
    self,
    rng: &mut R,
    verifier: &mut BatchVerifier<(), C::G>,
    transcript: &mut T,
    proof: SingleRangeProof<C>,
  ) {
    self.initial_transcript(transcript);

    let Self { generators, V } = self;
    let (y, _, _, _, A_hat) =
      Self::A_hat(transcript, generators.g(), generators.g_bold(), generators.h_bold(), V, proof.A);
    (WipStatement::new(generators, A_hat, y)).verify(rng, verifier, transcript, proof.wip);
  }
}
