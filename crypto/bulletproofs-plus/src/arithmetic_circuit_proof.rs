use rand_core::{RngCore, CryptoRng};

use zeroize::{Zeroize, ZeroizeOnDrop};

use transcript::Transcript;

use multiexp::{multiexp, BatchVerifier};
use ciphersuite::{
  group::{ff::Field, GroupEncoding},
  Ciphersuite,
};

use crate::{
  ScalarVector, ScalarMatrix, PointVector, Generators,
  weighted_inner_product::{WipStatement, WipWitness, WipProof},
  weighted_inner_product,
};

// Figure 4
#[derive(Clone, Debug, Zeroize)]
pub struct ArithmeticCircuitStatement<T: Transcript, C: Ciphersuite> {
  generators: Generators<T, C>,
  V: PointVector<C>,
  WL: ScalarMatrix<C>,
  WR: ScalarMatrix<C>,
  WO: ScalarMatrix<C>,
  WV: ScalarMatrix<C>,
  c: ScalarVector<C>,
}

#[derive(Clone, Debug, Zeroize, ZeroizeOnDrop)]
pub struct ArithmeticCircuitWitness<C: Ciphersuite> {
  pub(crate) aL: ScalarVector<C>,
  pub(crate) aR: ScalarVector<C>,
  pub(crate) aO: ScalarVector<C>,
  pub(crate) v: ScalarVector<C>,
  gamma: ScalarVector<C>,
}

impl<C: Ciphersuite> ArithmeticCircuitWitness<C> {
  pub fn new(
    aL: ScalarVector<C>,
    aR: ScalarVector<C>,
    v: ScalarVector<C>,
    gamma: ScalarVector<C>,
  ) -> Self {
    assert_eq!(aL.len(), aR.len());
    let mut aO = vec![];
    for (l, r) in aL.0.iter().zip(aR.0.iter()) {
      aO.push(*l * r);
    }
    let aO = ScalarVector(aO);

    assert_eq!(v.len(), gamma.len());
    ArithmeticCircuitWitness { aL, aR, aO, v, gamma }
  }
}

#[derive(Clone, Debug, Zeroize)]
pub struct ArithmeticCircuitProof<C: Ciphersuite> {
  pub(crate) A: C::G,
  wip: WipProof<C>,
}

impl<T: Transcript, C: Ciphersuite> ArithmeticCircuitStatement<T, C> {
  pub fn new(
    generators: Generators<T, C>,
    V: PointVector<C>,
    WL: ScalarMatrix<C>,
    WR: ScalarMatrix<C>,
    WO: ScalarMatrix<C>,
    WV: ScalarMatrix<C>,
    c: ScalarVector<C>,
  ) -> Self {
    let m = V.len();

    let q = WL.length();
    let n = WL.width();

    assert_eq!(WR.length(), q);
    assert_eq!(WR.width(), n);
    assert_eq!(WO.length(), q);
    assert_eq!(WO.width(), n);
    assert_eq!(WV.length(), q);
    assert_eq!(WV.width(), m);

    assert_eq!(c.len(), q);

    Self { generators, V, WL, WR, WO, WV, c }
  }

  fn initial_transcript(&self, transcript: &mut T) {
    transcript.domain_separate(b"arithmetic_circuit_proof");
    // TODO: Pre-transcript these? Pre-compile this entire proof?
    self.V.transcript(transcript, b"commitment");
    self.WL.transcript(transcript, b"WL");
    self.WR.transcript(transcript, b"WR");
    self.WO.transcript(transcript, b"WO");
    self.WV.transcript(transcript, b"WV");
    self.c.transcript(transcript, b"c");
  }

  fn transcript_A(transcript: &mut T, A: C::G) -> (C::F, C::F) {
    transcript.append_message(b"A", A.to_bytes());

    let y = C::hash_to_F(b"arithmetic_circuit_proof", transcript.challenge(b"y").as_ref());
    if bool::from(y.is_zero()) {
      panic!("zero challenge in arithmetic circuit proof");
    }

    let z = C::hash_to_F(b"arithmetic_circuit_proof", transcript.challenge(b"z").as_ref());
    if bool::from(z.is_zero()) {
      panic!("zero challenge in arithmetic circuit proof");
    }

    (y, z)
  }

  fn compute_A_hat(
    &self,
    transcript: &mut T,
    A: C::G,
  ) -> (C::F, C::F, ScalarVector<C>, ScalarVector<C>, ScalarVector<C>, ScalarVector<C>, C::G) {
    // TODO: First perform the WIP transcript before acquiring challenges
    let (y, z) = Self::transcript_A(transcript, A);

    let q = self.c.len();
    let n = self.WL.width();
    assert!(n != 0);

    let z2 = z * z;
    let mut z_q = vec![z];
    while z_q.len() < q {
      z_q.push(*z_q.last().unwrap() * z2);
    }
    let z_q = ScalarVector(z_q);

    let mut y_n = vec![y];
    let mut inv_y_n = vec![y.invert().unwrap()];
    while y_n.len() < n {
      y_n.push(*y_n.last().unwrap() * y);
      inv_y_n.push(*inv_y_n.last().unwrap() * inv_y_n[0]);
    }

    let t_y_z = |W: &ScalarMatrix<C>| {
      let res = W.mul_vec(&z_q).mul_vec(&ScalarVector(inv_y_n.clone()));
      assert_eq!(res.len(), n);
      res
    };
    let WL_y_z = t_y_z(&self.WL);
    let WR_y_z = t_y_z(&self.WR);
    let WO_y_z = t_y_z(&self.WO);

    let z_q_WV = self.WV.mul_vec(&z_q);
    assert_eq!(z_q_WV.len(), self.V.len());

    (
      y,
      *inv_y_n.last().unwrap(),
      z_q_WV.clone(),
      WL_y_z.clone(),
      WR_y_z.clone(),
      WO_y_z.clone(),
      A + self.generators.g_bold().mul_vec(&WR_y_z).sum() +
        self.generators.h_bold().mul_vec(&WL_y_z).sum() +
        self
          .generators
          .h_bold2()
          .mul_vec(&WO_y_z.sub(C::F::ONE).mul(inv_y_n.last().unwrap()))
          .sum() +
        self.V.mul_vec(&z_q_WV).sum() +
        (self.generators.g() *
          (z_q.inner_product(&self.c) +
            weighted_inner_product(&WR_y_z, &WL_y_z, &ScalarVector(y_n)))),
    )
  }

  pub fn prove_with_blind<R: RngCore + CryptoRng>(
    mut self,
    rng: &mut R,
    transcript: &mut T,
    mut witness: ArithmeticCircuitWitness<C>,
    blind: C::F,
  ) -> ArithmeticCircuitProof<C> {
    let m = self.V.len();

    assert_eq!(m, witness.v.len());
    assert_eq!(m, witness.gamma.len());

    for (commitment, (value, gamma)) in
      self.V.0.iter().zip(witness.v.0.iter().zip(witness.gamma.0.iter()))
    {
      assert_eq!(
        *commitment,
        multiexp(&[(*value, self.generators.g()), (*gamma, self.generators.h())])
      );
    }

    // aL * aR = aO doesn't need checking since we generate aO ourselves on witness creation
    debug_assert_eq!(witness.aL.len(), witness.aR.len());

    // TODO: Check WL WR WO WV

    self.generators.truncate(self.WL.width());

    self.initial_transcript(transcript);

    let alpha = blind;
    let A = self.generators.g_bold().mul_vec(&witness.aL).sum() +
      self.generators.g_bold2().mul_vec(&witness.aO).sum() +
      self.generators.h_bold().mul_vec(&witness.aR).sum() +
      (self.generators.h() * alpha);
    let (y, inv_y_n, z_q_WV, WL_y_z, WR_y_z, WO_y_z, A_hat) = self.compute_A_hat(transcript, A);

    let mut aL = witness.aL.add_vec(&WR_y_z);
    aL.0.append(&mut witness.aO.0);
    let mut aR = witness.aR.add_vec(&WL_y_z);
    aR.0.append(&mut WO_y_z.sub(C::F::ONE).mul(inv_y_n).0);
    let alpha = alpha + z_q_WV.inner_product(&witness.gamma);

    ArithmeticCircuitProof {
      A,
      wip: WipStatement::new(self.generators.reduce(self.WL.width(), true), A_hat, y).prove(
        rng,
        transcript,
        WipWitness::new(aL, aR, alpha),
      ),
    }
  }

  pub fn prove<R: RngCore + CryptoRng>(
    self,
    rng: &mut R,
    transcript: &mut T,
    witness: ArithmeticCircuitWitness<C>,
  ) -> ArithmeticCircuitProof<C> {
    let blind = C::F::random(&mut *rng);
    self.prove_with_blind(rng, transcript, witness, blind)
  }

  pub fn verify<R: RngCore + CryptoRng>(
    mut self,
    rng: &mut R,
    verifier: &mut BatchVerifier<(), C::G>,
    transcript: &mut T,
    proof: ArithmeticCircuitProof<C>,
  ) {
    self.generators.truncate(self.WL.width());
    self.initial_transcript(transcript);

    let (y, _, _, _, _, _, A_hat) = self.compute_A_hat(transcript, proof.A);
    (WipStatement::new(self.generators.reduce(self.WL.width(), true), A_hat, y))
      .verify(rng, verifier, transcript, proof.wip);
  }
}
