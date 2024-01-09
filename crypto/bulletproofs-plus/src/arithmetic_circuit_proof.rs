use rand_core::{RngCore, CryptoRng};

use zeroize::{Zeroize, ZeroizeOnDrop};

use transcript::Transcript;

use multiexp::{multiexp, multiexp_vartime, Point as MultiexpPoint, BatchVerifier};
use ciphersuite::{
  group::{ff::Field, Group, GroupEncoding},
  Ciphersuite,
};

use crate::{
  ScalarVector, ScalarMatrix, PointVector, GeneratorsList, ProofGenerators, padded_pow_of_2,
  inner_product::{IpStatement, IpWitness, IpProof},
};

// 5.1 Relation
#[derive(Clone, Debug)]
pub struct ArithmeticCircuitStatement<'a, T: 'static + Transcript, C: Ciphersuite> {
  generators: ProofGenerators<'a, T, C>,
  V: PointVector<C>,
  WL: ScalarMatrix<C>,
  WR: ScalarMatrix<C>,
  WO: ScalarMatrix<C>,
  WV: ScalarMatrix<C>,
  c: ScalarVector<C>,
}

impl<'a, T: 'static + Transcript, C: Ciphersuite> Zeroize for ArithmeticCircuitStatement<'a, T, C> {
  fn zeroize(&mut self) {
    self.V.zeroize();
    self.WL.zeroize();
    self.WR.zeroize();
    self.WO.zeroize();
    self.WV.zeroize();
    self.c.zeroize();
  }
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
  AI: C::G,
  AO: C::G,
  S: C::G,
  T1: C::G,
  T3: C::G,
  T4: C::G,
  T5: C::G,
  T6: C::G,
  tau_x: C::F,
  u: C::F,
  l: Vec<C::F>,
  r: Vec<C::F>,
  // TODO: Implement the logarithmically sized proof
  // ip: IpProof<C>,
}

impl<'a, T: 'static + Transcript, C: Ciphersuite> ArithmeticCircuitStatement<'a, T, C> {
  /// Create a new ArithmeticCircuitStatement for the specified relationship.
  ///
  /// The weights and c vector are not transcripted. They're expected to be deterministic from the
  /// static program and higher-level statement. If your constraints are variable with regards to
  /// variables which aren't the commitments, transcript as needed before calling prove/verify.
  pub fn new(
    generators: ProofGenerators<'a, T, C>,
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
    self.V.transcript(transcript, b"commitment");
  }

  fn transcript_AI_AO_S(
    transcript: &mut T,
    AI: C::G,
    AO: C::G,
    S: C::G,
    n: usize,
    q: usize,
  ) -> (ScalarVector<C>, ScalarVector<C>, ScalarVector<C>) {
    transcript.append_message(b"AI", AI.to_bytes());
    transcript.append_message(b"AO", AO.to_bytes());
    transcript.append_message(b"S", S.to_bytes());

    let y_1 = C::hash_to_F(b"arithmetic_circuit_proof", transcript.challenge(b"y").as_ref());
    if bool::from(y_1.is_zero()) {
      panic!("zero challenge in arithmetic circuit proof");
    }
    let inv_y_1 = y_1.invert().unwrap();
    let mut y = Vec::with_capacity(n);
    let mut inv_y = Vec::with_capacity(n);
    y.push(C::F::ONE);
    inv_y.push(C::F::ONE);
    while y.len() < n {
      y.push(*y.last().unwrap() * y_1);
      inv_y.push(*inv_y.last().unwrap() * inv_y_1);
    }

    let z_1 = C::hash_to_F(b"arithmetic_circuit_proof", transcript.challenge(b"z").as_ref());
    if bool::from(z_1.is_zero()) {
      panic!("zero challenge in arithmetic circuit proof");
    }
    let mut z = Vec::with_capacity(q);
    z.push(z_1);
    while z.len() < q {
      z.push(*z.last().unwrap() * z_1);
    }

    (ScalarVector(y), ScalarVector(inv_y), ScalarVector(z))
  }

  fn transcript_Ts(transcript: &mut T, T1: C::G, T3: C::G, T4: C::G, T5: C::G, T6: C::G) -> C::F {
    transcript.append_message(b"T1", T1.to_bytes());
    transcript.append_message(b"T3", T3.to_bytes());
    transcript.append_message(b"T4", T4.to_bytes());
    transcript.append_message(b"T5", T5.to_bytes());
    transcript.append_message(b"T6", T6.to_bytes());

    let x = C::hash_to_F(b"arithmetic_circuit_proof", transcript.challenge(b"x").as_ref());
    if bool::from(x.is_zero()) {
      panic!("zero challenge in arithmetic circuit proof");
    }
    x
  }

  pub fn prove<R: RngCore + CryptoRng>(
    self,
    rng: &mut R,
    transcript: &mut T,
    mut witness: ArithmeticCircuitWitness<C>,
  ) -> ArithmeticCircuitProof<C> {
    let m = self.V.len();
    let n = witness.aL.len();
    assert_eq!(self.WL.width(), n);
    let q = self.WL.length();

    assert_eq!(m, witness.v.len());
    assert_eq!(m, witness.gamma.len());

    for (commitment, (value, gamma)) in
      self.V.0.iter().zip(witness.v.0.iter().zip(witness.gamma.0.iter()))
    {
      assert_eq!(
        *commitment,
        multiexp(&[(*value, self.generators.g().point()), (*gamma, self.generators.h().point())])
      );
    }

    // aL * aR = aO doesn't need checking since we generate aO ourselves on witness creation
    debug_assert_eq!(witness.aL.len(), witness.aR.len());

    // TODO: Check WL WR WO WV

    self.initial_transcript(transcript);

    let alpha = C::F::random(&mut *rng);
    let beta = C::F::random(&mut *rng);
    let p = C::F::random(&mut *rng);
    let mut AI_terms = Vec::with_capacity((witness.aL.len() * 2) + 1);
    for (i, aL) in witness.aL.0.iter().enumerate() {
      AI_terms.push((*aL, self.generators.generator(GeneratorsList::GBold1, i).point()));
    }
    for (i, aR) in witness.aR.0.iter().enumerate() {
      AI_terms.push((*aR, self.generators.generator(GeneratorsList::HBold1, i).point()));
    }
    AI_terms.push((alpha, self.generators.h().point()));
    let AI = multiexp(&AI_terms);
    AI_terms.zeroize();

    let mut AO_terms = Vec::with_capacity(witness.aL.len() + 1);
    for (i, aO) in witness.aO.0.iter().enumerate() {
      AO_terms.push((*aO, self.generators.generator(GeneratorsList::GBold1, i).point()));
    }
    AO_terms.push((beta, self.generators.h().point()));
    let AO = multiexp(&AO_terms);
    AO_terms.zeroize();

    let mut sL = vec![];
    let mut sR = vec![];
    let mut S_terms = Vec::with_capacity((witness.aL.len() * 2) + 1);
    for i in 0 .. n {
      let new_sL = C::F::random(&mut *rng);
      sL.push(new_sL);
      S_terms.push((new_sL, self.generators.generator(GeneratorsList::GBold1, i).point()));
      let new_sR = C::F::random(&mut *rng);
      sR.push(new_sR);
      S_terms.push((new_sR, self.generators.generator(GeneratorsList::HBold1, i).point()));
    }
    S_terms.push((p, self.generators.h().point()));
    let S = multiexp(&S_terms);
    S_terms.zeroize();

    let (y, inv_y, z) = Self::transcript_AI_AO_S(transcript, AI, AO, S, n, q);
    let delta = inv_y.mul_vec(&self.WR.mul_vec(&z)).inner_product(&self.WL.mul_vec(&z));

    let l1_coeff = witness.aL.add_vec(&inv_y.mul_vec(&self.WR.mul_vec(&z)));
    let l2_coeff = &witness.aO;
    let l3_coeff = ScalarVector(sL.clone());

    let r0_coeff = self.WO.mul_vec(&z).sub_vec(&y);
    let r1_coeff = self.WL.mul_vec(&z).add_vec(&y.mul_vec(&witness.aR));
    let r3_coeff = y.mul_vec(&ScalarVector(sR.clone()));

    let l = |X: C::F| -> ScalarVector<_> {
      let X2 = X.square();
      l1_coeff.mul(X).add_vec(&l2_coeff.mul(X2)).add_vec(&l3_coeff.mul(X2 * X))
    };
    let r = |X: C::F| -> ScalarVector<_> {
      r0_coeff.add_vec(&r1_coeff.mul(X)).add_vec(&r3_coeff.mul(X.square() * X))
    };
    let t = |X: C::F| -> C::F { l(X).inner_product(&r(X)) };

    /*
    let w = self
      .WL
      .mul_vec(&witness.aL)
      .add_vec(&self.WR.mul_vec(&witness.aR))
      .add_vec(&self.WO.mul_vec(&witness.aO));
    */

    // t1 = (l1 * r0)
    // t2 = (l1 * r1) + (l2 * r0)
    // t3 = (l2 * r1) + (l3 * r0)
    // t4 = (l1 * r3) + (l3 * r1)
    // t5 = (l2 * r3)
    // t6 = (l3 * r3)

    let t1 = l1_coeff.inner_product(&r0_coeff);
    let t2 = l1_coeff.inner_product(&r1_coeff) + l2_coeff.inner_product(&r0_coeff);
    let t3 = l2_coeff.inner_product(&r1_coeff) + l3_coeff.inner_product(&r0_coeff);
    let t4 = l1_coeff.inner_product(&r3_coeff) + l3_coeff.inner_product(&r1_coeff);
    let t5 = l2_coeff.inner_product(&r3_coeff);
    let t6 = l3_coeff.inner_product(&r3_coeff);

    {
      let dummy_X = C::F::random(&mut *rng);
      let dummy_X2 = dummy_X.square();
      let dummy_X3 = dummy_X2 * dummy_X;
      let dummy_X4 = dummy_X3 * dummy_X;
      let dummy_X5 = dummy_X4 * dummy_X;
      let dummy_X6 = dummy_X5 * dummy_X;
      assert_eq!(
        t(dummy_X),
        (t1 * dummy_X) +
          (t2 * dummy_X2) +
          (t3 * dummy_X3) +
          (t4 * dummy_X4) +
          (t5 * dummy_X5) +
          (t6 * dummy_X6)
      );
    }

    /*
    let t2 = witness.aL.inner_product(&witness.aR.mul_vec(&y)) - witness.aO.inner_product(&y) +
      z.inner_product(&w) +
      delta;
    */

    let tau_1 = C::F::random(&mut *rng);
    let tau_3 = C::F::random(&mut *rng);
    let tau_4 = C::F::random(&mut *rng);
    let tau_5 = C::F::random(&mut *rng);
    let tau_6 = C::F::random(&mut *rng);
    let T1 = multiexp(&[(t1, self.generators.g().point()), (tau_1, self.generators.h().point())]);
    let T3 = multiexp(&[(t3, self.generators.g().point()), (tau_3, self.generators.h().point())]);
    let T4 = multiexp(&[(t4, self.generators.g().point()), (tau_4, self.generators.h().point())]);
    let T5 = multiexp(&[(t5, self.generators.g().point()), (tau_5, self.generators.h().point())]);
    let T6 = multiexp(&[(t6, self.generators.g().point()), (tau_6, self.generators.h().point())]);

    let x = Self::transcript_Ts(transcript, T1, T3, T4, T5, T6);
    let l = l(x);
    let r = r(x);
    let tau_x = (tau_1 * x) +
      (self.WV.mul_vec(&z).inner_product(&witness.gamma) * x.square()) +
      // (z.inner_product(&self.WV.mul_vec(&witness.gamma)) * x.square()) +
      (tau_3 * x.square() * x) +
      (tau_4 * x.square().square()) +
      (tau_5 * x.square().square() * x) +
      (tau_6 * x.square().square() * x.square());
    let u = (alpha * x) + (beta * x.square()) + (p * x.square() * x);

    ArithmeticCircuitProof { AI, AO, S, T1, T3, T4, T5, T6, tau_x, u, l: l.0, r: r.0 }
  }

  pub fn verify<R: RngCore + CryptoRng>(
    self,
    rng: &mut R,
    verifier: &mut BatchVerifier<(), C::G>,
    transcript: &mut T,
    proof: ArithmeticCircuitProof<C>,
  ) {
    let m = self.V.len();
    let n = self.WL.width();
    let q = self.WL.length();

    self.initial_transcript(transcript);
    let (y, inv_y, z) = Self::transcript_AI_AO_S(transcript, proof.AI, proof.AO, proof.S, n, q);
    let delta = inv_y.mul_vec(&self.WR.mul_vec(&z)).inner_product(&self.WL.mul_vec(&z));
    let x = Self::transcript_Ts(transcript, proof.T1, proof.T3, proof.T4, proof.T5, proof.T6);

    let reduced = self.generators.reduce(n, true);
    // TODO: Always keep the following in terms of the original generators to allow de-duplication
    // within the multiexp
    let mut hi = vec![];
    for i in 0 .. n {
      hi.push(reduced.generator(GeneratorsList::HBold1, i).point() * inv_y[i]);
    }
    assert_eq!(reduced.generator(GeneratorsList::HBold1, 0).point(), hi[0]);
    let hi = PointVector(hi);
    let WL = hi.mul_vec(&self.WL.mul_vec(&z));
    let mut WR = vec![];
    let w_r_scalars = inv_y.mul_vec(&self.WR.mul_vec(&z));
    for i in 0 .. n {
      WR.push(reduced.generator(GeneratorsList::GBold1, i).point() * w_r_scalars.0[i]);
    }
    let WR = PointVector::<C>(WR);
    let WO = hi.mul_vec(&self.WO.mul_vec(&z));

    let t_caret = ScalarVector::<C>(proof.l.clone()).inner_product(&ScalarVector(proof.r.clone()));
    let x_square = x.square();
    let x_tesseract = x_square * x_square;
    let Ts = (proof.T3 * (x_square * x) +
      (proof.T4 * x_tesseract) +
      (proof.T5 * (x_tesseract * x)) +
      (proof.T6 * (x_tesseract * x_square));
    // TODO: Queue this as a batch verification statement
    assert!(bool::from(
      (multiexp_vartime(&[
        (t_caret - (x_square * (delta + z.inner_product(&self.c))), reduced.g().point()),
        (proof.tau_x, reduced.h().point()),
        (-x, proof.T1)
      ]) - self.V.mul_vec(&self.WV.mul_vec(&z).mul(x_square)).sum() -
        Ts)
        .is_identity()
    ));

    // h' ** y is equivalent to h as h' is h ** inv_y
    // TOOD: Cache this as a long lived generator
    let mut h_sum = reduced.generator(GeneratorsList::HBold1, 0).point();
    for i in 1 .. n {
      h_sum += reduced.generator(GeneratorsList::HBold1, i).point();
    }
    let mut P_terms = vec![
      (C::F::ONE, WO.sum() - h_sum),
      (x, proof.AI + WL.sum() + WR.sum()),
      (x_square, proof.AO),
      (x_square * x, proof.S),
    ];
    let P = multiexp_vartime(&P_terms);

    /* TODO: Move this to the logarithmic IP proof and batch verify
    // P is deterministic to transcripted variables
    IpProof::new_without_P_transcript(reduced, vec![
      (x, proof.AI),
      (x_square, proof.AO),
    ])
    */

    let mut rhs = reduced.h().point() * proof.u;
    for (i, (l, r)) in proof.l.into_iter().zip(proof.r.into_iter()).enumerate() {
      rhs += reduced.generator(GeneratorsList::GBold1, i).point() * l;
      rhs += hi[i] * r;
    }
    assert_eq!(P, rhs);
  }
}
