use rand_core::{RngCore, CryptoRng};

use zeroize::{Zeroize, ZeroizeOnDrop};

use transcript::Transcript;

use multiexp::{multiexp, Point as MultiexpPoint, BatchVerifier};
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
    assert_eq!(v.len(), gamma.len());

    let aO = aL.mul_vec(&aR);
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

    // Determine q/n by WL length/width
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
  ) -> (
    ScalarVector<C>,
    C::F,
    ScalarVector<C>,
    ScalarVector<C>,
    ScalarVector<C>,
    ScalarVector<C>,
    Vec<(C::F, MultiexpPoint<C::G>)>,
  ) {
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
    let inv_y_n = ScalarVector(inv_y_n);

    //let z_q_inv_y_n = z_q.mul_vec(&inv_y_n);

    let t_y_z = |W: &ScalarMatrix<C>| {
      // TODO: Can these latter two mul_vecs be merged?
      let res = W.mul_vec(&z_q).mul_vec(&inv_y_n);
      assert_eq!(res.len(), n);
      res
    };
    let WL_y_z = t_y_z(&self.WL);
    let WR_y_z = t_y_z(&self.WR);
    let WO_y_z = t_y_z(&self.WO);

    let z_q_WV = self.WV.mul_vec(&z_q);
    assert_eq!(z_q_WV.len(), self.V.len());

    // TODO: Move to constants once the generators object handles constant labelling
    let mut A_terms = Vec::with_capacity(1 + (3 * self.c.len()) + self.V.len() + 1);
    A_terms.push((C::F::ONE, MultiexpPoint::Variable(A)));
    for pair in WR_y_z.0.iter().zip(self.generators.multiexp_g_bold().iter()) {
      A_terms.push((*pair.0, pair.1.clone()));
    }
    for pair in WL_y_z.0.iter().zip(self.generators.multiexp_h_bold().iter()) {
      A_terms.push((*pair.0, pair.1.clone()));
    }
    for pair in WO_y_z.0.iter().zip(self.generators.multiexp_h_bold2().iter()) {
      A_terms.push(((*pair.0 - C::F::ONE) * inv_y_n.0.last().unwrap(), pair.1.clone()));
    }
    for pair in z_q_WV.0.iter().zip(self.V.0.iter()) {
      A_terms.push((*pair.0, MultiexpPoint::Variable(*pair.1)));
    }
    let y_n = ScalarVector(y_n);
    A_terms.push((
      z_q.inner_product(&self.c) + weighted_inner_product(&WR_y_z, &WL_y_z, &y_n),
      self.generators.multiexp_g(),
    ));

    (y_n, *inv_y_n.0.last().unwrap(), z_q_WV, WL_y_z, WR_y_z, WO_y_z, A_terms)
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
    let mut A_terms = Vec::with_capacity((self.generators.multiexp_g_bold().len() * 3) + 1);
    for (g_bold, aL) in self.generators.multiexp_g_bold().iter().zip(&witness.aL.0) {
      A_terms.push((*aL, g_bold.point()));
    }
    for (h_bold, aR) in self.generators.multiexp_h_bold().iter().zip(&witness.aR.0) {
      A_terms.push((*aR, h_bold.point()));
    }
    for (g_bold2, aO) in self.generators.multiexp_g_bold2().iter().zip(&witness.aO.0) {
      A_terms.push((*aO, g_bold2.point()));
    }
    A_terms.push((alpha, self.generators.h()));
    let A = multiexp(&A_terms);
    A_terms.zeroize();

    let (y, inv_y_n, z_q_WV, WL_y_z, WR_y_z, WO_y_z, A_hat) = self.compute_A_hat(transcript, A);

    let mut aL = witness.aL.add_vec(&WR_y_z);
    aL.0.append(&mut witness.aO.0);
    let mut aR = witness.aR.add_vec(&WL_y_z);
    aR.0.append(&mut WO_y_z.sub(C::F::ONE).mul(inv_y_n).0);
    let alpha = alpha + z_q_WV.inner_product(&witness.gamma);

    // Safe to not transcript A_hat since A_hat is solely derivative of transcripted values
    ArithmeticCircuitProof {
      A,
      wip: WipStatement::new_without_P_transcript(
        self.generators.reduce(self.WL.width(), true),
        A_hat,
        y,
      )
      .prove(rng, transcript, WipWitness::new(aL, aR, alpha)),
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
    (WipStatement::new_without_P_transcript(
      self.generators.reduce(self.WL.width(), true),
      A_hat,
      y,
    ))
    .verify(rng, verifier, transcript, proof.wip);
  }
}
