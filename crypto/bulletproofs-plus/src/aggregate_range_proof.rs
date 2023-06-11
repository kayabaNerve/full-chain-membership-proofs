use rand_core::{RngCore, CryptoRng};

use zeroize::{Zeroize, ZeroizeOnDrop};

use transcript::Transcript;

use multiexp::BatchVerifier;
use ciphersuite::{
  group::{ff::Field, Group, GroupEncoding},
  Ciphersuite,
};

use crate::{
  RANGE_PROOF_BITS, ScalarVector, PointVector, Generators, RangeCommitment,
  weighted_inner_product::{WipStatement, WipWitness, WipProof},
  u64_decompose,
};

const N: usize = RANGE_PROOF_BITS;

// Figure 3
#[derive(Clone, Debug, Zeroize)]
pub struct AggregateRangeStatement<T: Transcript, C: Ciphersuite> {
  generators: Generators<T, C>,
  V: PointVector<C>,
}

#[derive(Clone, Debug, Zeroize, ZeroizeOnDrop)]
pub struct AggregateRangeWitness<C: Ciphersuite> {
  values: Vec<u64>,
  gammas: Vec<C::F>,
}

impl<C: Ciphersuite> AggregateRangeWitness<C> {
  pub fn new(commitments: &[RangeCommitment<C>]) -> Self {
    let mut values = vec![];
    let mut gammas = vec![];
    for commitment in commitments {
      values.push(commitment.value);
      gammas.push(commitment.mask);
    }
    AggregateRangeWitness { values, gammas }
  }
}

#[derive(Clone, Debug, Zeroize)]
pub struct AggregateRangeProof<C: Ciphersuite> {
  A: C::G,
  wip: WipProof<C>,
}

impl<T: Transcript, C: Ciphersuite> AggregateRangeStatement<T, C> {
  pub fn new(generators: Generators<T, C>, V: Vec<C::G>) -> Self {
    assert!(!V.is_empty());
    Self { generators, V: PointVector(V) }
  }

  fn initial_transcript(&self, transcript: &mut T) {
    transcript.domain_separate(b"aggregate_range_proof");
    for V in &self.V.0 {
      transcript.append_message(b"commitment", V.to_bytes());
    }
  }

  fn transcript_A(transcript: &mut T, A: C::G) -> (C::F, C::F) {
    transcript.append_message(b"A", A.to_bytes());

    let y = C::hash_to_F(b"aggregate_range_proof", transcript.challenge(b"y").as_ref());
    if bool::from(y.is_zero()) {
      panic!("zero challenge in aggregate range proof");
    }

    let z = C::hash_to_F(b"aggregate_range_proof", transcript.challenge(b"z").as_ref());
    if bool::from(z.is_zero()) {
      panic!("zero challenge in aggregate range proof");
    }

    (y, z)
  }

  fn d_j(j: usize, m: usize) -> ScalarVector<C> {
    let mut d_j = vec![];
    for _ in 0 .. (j - 1) * N {
      d_j.push(C::F::ZERO);
    }
    d_j.append(&mut ScalarVector::<C>::powers(C::F::from(2), RANGE_PROOF_BITS).0);
    for _ in 0 .. (m - j) * N {
      d_j.push(C::F::ZERO);
    }
    ScalarVector(d_j)
  }

  fn compute_A_hat(
    &self,
    transcript: &mut T,
    A: C::G,
  ) -> (C::F, ScalarVector<C>, C::F, ScalarVector<C>, ScalarVector<C>, C::G) {
    // TODO: First perform the WIP transcript before acquiring challenges
    let (y, z) = Self::transcript_A(transcript, A);

    assert_eq!(self.generators.g_bold().len(), self.V.len() * N);

    let mut z_pow = vec![];

    let mn = self.V.len() * N;
    let mut d = ScalarVector::new(mn);
    for j in 1 ..= self.V.len() {
      z_pow.push(z.pow([2 * u64::try_from(j).unwrap()])); // TODO: Optimize this
      d = d.add_vec(&Self::d_j(j, self.V.len()).mul(z_pow[j - 1]));
    }

    let mut ascending_y = ScalarVector(vec![y]);
    for i in 1 .. mn {
      ascending_y.0.push(ascending_y[i - 1] * y);
    }
    let y_pows = ascending_y.clone().sum();

    let mut descending_y = ascending_y.clone();
    descending_y.0.reverse();

    let d_descending_y = d.mul_vec(&descending_y);

    let y_mn_plus_one = descending_y[0] * y;
    debug_assert_eq!(y_mn_plus_one, y.pow([u64::try_from(mn).unwrap() + 1]));

    let mut commitment_accum = C::G::identity();
    for (j, commitment) in self.V.0.iter().enumerate() {
      commitment_accum += *commitment * z_pow[j];
    }

    // Collapse of [1; mn] * z
    let z_vec = ScalarVector(vec![z; mn]);

    (
      y,
      d_descending_y.clone(),
      y_mn_plus_one,
      z_vec.clone(),
      ScalarVector(z_pow),
      A + self.generators.g_bold().mul_vec(&ScalarVector(vec![-z; mn])).sum() +
        self.generators.h_bold().mul_vec(&d_descending_y.add_vec(&z_vec)).sum() +
        (commitment_accum * y_mn_plus_one) +
        (self.generators.g() *
          ((y_pows * z) - (d.sum() * y_mn_plus_one * z) - (y_pows * z.square()))),
    )
  }

  pub fn prove<R: RngCore + CryptoRng>(
    self,
    rng: &mut R,
    transcript: &mut T,
    witness: AggregateRangeWitness<C>,
  ) -> AggregateRangeProof<C> {
    assert_eq!(self.V.len(), witness.values.len());
    debug_assert_eq!(witness.values.len(), witness.gammas.len());
    for (commitment, (value, gamma)) in
      self.V.0.iter().zip(witness.values.iter().zip(witness.gammas.iter()))
    {
      debug_assert_eq!(
        RangeCommitment::<C>::new(*value, *gamma)
          .calculate(self.generators.g(), self.generators.h()),
        *commitment
      );
    }

    self.initial_transcript(transcript);

    let mut d_js = vec![];
    let mut a_l = ScalarVector(vec![]);
    for j in 1 ..= self.V.len() {
      d_js.push(Self::d_j(j, self.V.len()));
      a_l.0.append(&mut u64_decompose::<C>(witness.values[j - 1]).0);
    }

    for (value, d_j) in witness.values.iter().zip(d_js.iter()) {
      debug_assert_eq!(d_j.len(), a_l.len());
      debug_assert_eq!(a_l.inner_product(d_j), C::F::from(*value));
    }

    let a_r = a_l.sub(C::F::ONE);

    let g_bold = self.generators.g_bold();
    let h_bold = self.generators.h_bold();

    let alpha = C::F::random(&mut *rng);
    let A = g_bold.mul_vec(&a_l).sum() + h_bold.mul_vec(&a_r).sum() + (self.generators.h() * alpha);

    let (y, d_descending_y, y_mn_plus_one, z_vec, z_pow, A_hat) = self.compute_A_hat(transcript, A);

    let a_l = a_l.sub_vec(&z_vec);
    let a_r = a_r.add_vec(&d_descending_y).add_vec(&z_vec);
    let mut alpha = alpha;
    for j in 1 ..= witness.gammas.len() {
      alpha += z_pow[j - 1] * witness.gammas[j - 1] * y_mn_plus_one;
    }

    AggregateRangeProof {
      A,
      wip: WipStatement::new(self.generators, A_hat, y).prove(
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
    proof: AggregateRangeProof<C>,
  ) {
    self.initial_transcript(transcript);

    let (y, _, _, _, _, A_hat) = self.compute_A_hat(transcript, proof.A);
    (WipStatement::new(self.generators, A_hat, y)).verify(rng, verifier, transcript, proof.wip);
  }
}
