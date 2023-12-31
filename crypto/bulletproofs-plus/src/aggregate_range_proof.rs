use rand_core::{RngCore, CryptoRng};

use zeroize::{Zeroize, ZeroizeOnDrop};

use transcript::Transcript;

use multiexp::{multiexp, multiexp_vartime, Point as MultiexpPoint, BatchVerifier};
use ciphersuite::{
  group::{ff::Field, Group, GroupEncoding},
  Ciphersuite,
};

use crate::{
  RANGE_PROOF_BITS, ScalarVector, PointVector, GeneratorsList, ProofGenerators,
  InnerProductGenerators, RangeCommitment,
  weighted_inner_product::{WipStatement, WipWitness, WipProof},
  u64_decompose,
};

const N: usize = RANGE_PROOF_BITS;

// Figure 3
#[derive(Clone, Debug)]
pub struct AggregateRangeStatement<'a, T: 'static + Transcript, C: Ciphersuite> {
  generators: ProofGenerators<'a, T, C>,
  V: PointVector<C>,
}

impl<'a, T: 'static + Transcript, C: Ciphersuite> Zeroize for AggregateRangeStatement<'a, T, C> {
  fn zeroize(&mut self) {
    self.V.zeroize();
  }
}

#[derive(Clone, Debug, Zeroize, ZeroizeOnDrop)]
pub struct AggregateRangeWitness<C: Ciphersuite> {
  values: Vec<u64>,
  gammas: Vec<C::F>,
}

impl<C: Ciphersuite> AggregateRangeWitness<C> {
  pub fn new(commitments: &[RangeCommitment<C>]) -> Self {
    let mut values = Vec::with_capacity(commitments.len());
    let mut gammas = Vec::with_capacity(commitments.len());
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

impl<'a, T: 'static + Transcript, C: Ciphersuite> AggregateRangeStatement<'a, T, C> {
  pub fn new(generators: ProofGenerators<'a, T, C>, V: Vec<C::G>) -> Self {
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
    let mut d_j = Vec::with_capacity(m * RANGE_PROOF_BITS);
    for _ in 0 .. (j - 1) * N {
      d_j.push(C::F::ZERO);
    }
    d_j.append(&mut ScalarVector::<C>::powers(C::F::from(2), RANGE_PROOF_BITS).0);
    for _ in 0 .. (m - j) * N {
      d_j.push(C::F::ZERO);
    }
    ScalarVector(d_j)
  }

  fn compute_A_hat<GB: Clone + AsRef<[MultiexpPoint<C::G>]>>(
    V: &PointVector<C>,
    generators: &InnerProductGenerators<'a, T, C, GB>,
    transcript: &mut T,
    A: C::G,
  ) -> (C::F, ScalarVector<C>, C::F, C::F, ScalarVector<C>, C::G) {
    // TODO: First perform the WIP transcript before acquiring challenges
    let (y, z) = Self::transcript_A(transcript, A);

    let mn = V.len() * N;

    let mut z_pow = Vec::with_capacity(V.len());

    let mut d = ScalarVector::new(mn);
    for j in 1 ..= V.len() {
      z_pow.push(z.pow([2 * u64::try_from(j).unwrap()])); // TODO: Optimize this
      d = d.add_vec(&Self::d_j(j, V.len()).mul(z_pow[j - 1]));
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
    for (j, commitment) in V.0.iter().enumerate() {
      commitment_accum += *commitment * z_pow[j];
    }

    let neg_z = -z;
    let mut A_terms = Vec::with_capacity((generators.len() * 2) + 2);
    for (i, d_y_z) in d_descending_y.add(z).0.drain(..).enumerate() {
      A_terms.push((neg_z, generators.generator(GeneratorsList::GBold1, i).point()));
      A_terms.push((d_y_z, generators.generator(GeneratorsList::HBold1, i).point()));
    }
    A_terms.push((y_mn_plus_one, commitment_accum));
    A_terms.push((
      ((y_pows * z) - (d.sum() * y_mn_plus_one * z) - (y_pows * z.square())),
      generators.g().point(),
    ));

    (y, d_descending_y, y_mn_plus_one, z, ScalarVector(z_pow), A + multiexp_vartime(&A_terms))
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
          .calculate(self.generators.g().point(), self.generators.h().point()),
        *commitment
      );
    }

    self.initial_transcript(transcript);

    let Self { generators, V } = self;
    let generators = generators.reduce(V.len() * RANGE_PROOF_BITS, false);

    let mut d_js = Vec::with_capacity(V.len());
    let mut a_l = ScalarVector(Vec::with_capacity(V.len() * RANGE_PROOF_BITS));
    for j in 1 ..= V.len() {
      d_js.push(Self::d_j(j, V.len()));
      a_l.0.append(&mut u64_decompose::<C>(witness.values[j - 1]).0);
    }

    for (value, d_j) in witness.values.iter().zip(d_js.iter()) {
      debug_assert_eq!(d_j.len(), a_l.len());
      debug_assert_eq!(a_l.inner_product(d_j), C::F::from(*value));
    }

    let a_r = a_l.sub(C::F::ONE);

    let alpha = C::F::random(&mut *rng);

    let mut A_terms = Vec::with_capacity((generators.len() * 2) + 1);
    for (i, a_l) in a_l.0.iter().enumerate() {
      A_terms.push((*a_l, generators.generator(GeneratorsList::GBold1, i).point()));
    }
    for (i, a_r) in a_r.0.iter().enumerate() {
      A_terms.push((*a_r, generators.generator(GeneratorsList::HBold1, i).point()));
    }
    A_terms.push((alpha, generators.h().point()));
    let A = multiexp(&A_terms);
    A_terms.zeroize();

    let (y, d_descending_y, y_mn_plus_one, z, z_pow, A_hat) =
      Self::compute_A_hat(&V, &generators, transcript, A);

    let a_l = a_l.sub(z);
    let a_r = a_r.add_vec(&d_descending_y).add(z);
    let mut alpha = alpha;
    for j in 1 ..= witness.gammas.len() {
      alpha += z_pow[j - 1] * witness.gammas[j - 1] * y_mn_plus_one;
    }

    AggregateRangeProof {
      A,
      wip: WipStatement::new(&generators, A_hat, y).prove(
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

    let Self { generators, V } = self;
    let generators = generators.reduce(V.len() * RANGE_PROOF_BITS, false);

    let (y, _, _, _, _, A_hat) = Self::compute_A_hat(&V, &generators, transcript, proof.A);
    (WipStatement::new(&generators, A_hat, y)).verify(rng, verifier, transcript, proof.wip);
  }
}
