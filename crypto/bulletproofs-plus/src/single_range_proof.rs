use rand_core::{RngCore, CryptoRng};

use zeroize::{Zeroize, ZeroizeOnDrop};

use transcript::Transcript;

use ciphersuite::{
  group::{
    ff::{Field, PrimeField},
    GroupEncoding,
  },
  Ciphersuite,
};

use crate::{
  BulletproofsCurve, ScalarVector, PointVector, Commitment,
  weighted_inner_product::{WipStatement, WipWitness, WipProof},
  u64_decompose, weighted_inner_product,
};

// Figure 2
#[derive(Clone, Debug, Zeroize)]
pub struct SingleRangeStatement<C: Ciphersuite> {
  g_bold: PointVector<C>,
  h_bold: PointVector<C>,
  V: C::G,
}

#[derive(Clone, Debug, Zeroize, ZeroizeOnDrop)]
pub struct SingleRangeWitness<C: Ciphersuite> {
  value: u64,
  gamma: C::F,
}

impl<C: BulletproofsCurve> SingleRangeWitness<C> {
  pub fn new(commitment: Commitment<C>) -> Self {
    SingleRangeWitness { value: commitment.value, gamma: commitment.mask }
  }
}

#[derive(Clone, Debug, Zeroize)]
pub struct SingleRangeProof<C: Ciphersuite> {
  A: C::G,
  wip: WipProof<C>,
}

impl<C: BulletproofsCurve> SingleRangeStatement<C> {
  pub fn new(g_bold: PointVector<C>, h_bold: PointVector<C>, V: C::G) -> Self {
    assert_eq!(g_bold.len(), 64); // 64-bit range proof
    assert_eq!(g_bold.len(), h_bold.len());

    Self { g_bold, h_bold, V }
  }

  fn initial_transcript<T: Transcript>(&self, transcript: &mut T) {
    transcript.domain_separate(b"single_range_proof");
    transcript.append_message(b"commitment", self.V.to_bytes());
  }

  fn transcript_A<T: Transcript>(transcript: &mut T, A: C::G) -> (C::F, C::F) {
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

  fn A_hat<T: Transcript>(
    transcript: &mut T,
    g_bold: &PointVector<C>,
    h_bold: &PointVector<C>,
    V: C::G,
    A: C::G,
  ) -> (C::F, ScalarVector<C>, C::F, ScalarVector<C>, C::G) {
    // TODO: First perform the WIP transcript before acquiring challenges
    let (y, z) = Self::transcript_A(transcript, A);

    let one_vec = ScalarVector::<C>(vec![C::F::ONE; 64]);
    let two_pows = ScalarVector::powers(C::F::from(2), 64);
    debug_assert_eq!(two_pows[0], C::F::ONE);
    debug_assert_eq!(two_pows[63], C::F::from(2).pow(&[63]));
    debug_assert!(two_pows.0.get(64).is_none());
    // Collapse of [1; 64] * z
    let z_vec = ScalarVector(vec![z; 64]);

    let mut ascending_y = ScalarVector(vec![y]);
    for i in 1 .. 64 {
      ascending_y.0.push(ascending_y[i - 1] * y);
    }

    let mut descending_y = ascending_y.clone();
    descending_y.0.reverse();

    let y_n_plus_one = descending_y[0] * y;
    debug_assert_eq!(y_n_plus_one, y.pow(&[64 + 1]));
    let y_pows = ascending_y.sum();

    let two_descending_y = two_pows.mul_vec(&descending_y);
    (
      y,
      two_descending_y.clone(),
      y_n_plus_one,
      z_vec.clone(),
      A + g_bold.mul_vec(&ScalarVector(vec![-z; 64])).sum() +
        h_bold.mul_vec(&two_descending_y.add_vec(&z_vec)).sum() +
        (V * y_n_plus_one) +
        (C::generator() *
          ((y_pows * z) - (two_pows.sum() * y_n_plus_one * z) - (y_pows * z.square()))),
    )
  }

  pub fn prove<R: RngCore + CryptoRng, T: Transcript>(
    self,
    rng: &mut R,
    transcript: &mut T,
    witness: SingleRangeWitness<C>,
  ) -> SingleRangeProof<C> {
    self.initial_transcript(transcript);

    let alpha = C::F::random(&mut *rng);
    let a_l = u64_decompose::<C>(witness.value);
    debug_assert_eq!(
      a_l.inner_product(&ScalarVector::powers(C::F::from(2), 64)),
      C::F::from(witness.value),
    );
    let a_r = a_l.sub(C::F::ONE);
    debug_assert!(bool::from(a_l.inner_product(&a_r).is_zero()));

    let Self { g_bold, h_bold, V } = self;
    let A = g_bold.mul_vec(&a_l).sum() + h_bold.mul_vec(&a_r).sum() + (C::alt_generator() * alpha);
    let (y, two_descending_y, y_n_plus_one, z_vec, A_hat) =
      Self::A_hat(transcript, &g_bold, &h_bold, V, A);

    let a_l = a_l.sub_vec(&z_vec);
    let a_r = a_r.add_vec(&two_descending_y).add_vec(&z_vec);
    let alpha = alpha + (witness.gamma * y_n_plus_one);

    SingleRangeProof {
      A,
      wip: WipStatement::new(g_bold, h_bold, A_hat).prove(
        rng,
        transcript,
        WipWitness::new(a_l, a_r, alpha),
        y,
      ),
    }
  }

  // TODO: Use a BatchVerifier
  pub fn verify<T: Transcript>(self, transcript: &mut T, proof: SingleRangeProof<C>) {
    self.initial_transcript(transcript);

    let Self { g_bold, h_bold, V } = self;
    let (y, _, _, _, A_hat) = Self::A_hat(transcript, &g_bold, &h_bold, V, proof.A);
    (WipStatement::new(g_bold, h_bold, A_hat)).verify(transcript, proof.wip, y);
  }
}
