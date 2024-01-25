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
  C: PointVector<C>,
  WL: ScalarMatrix<C>,
  WR: ScalarMatrix<C>,
  WO: ScalarMatrix<C>,
  WV: ScalarMatrix<C>,
  WC: Vec<ScalarMatrix<C>>,
  c: ScalarVector<C>,
}

impl<'a, T: 'static + Transcript, C: Ciphersuite> Zeroize for ArithmeticCircuitStatement<'a, T, C> {
  fn zeroize(&mut self) {
    self.V.zeroize();
    self.C.zeroize();
    self.WL.zeroize();
    self.WR.zeroize();
    self.WO.zeroize();
    self.WV.zeroize();
    self.WC.zeroize();
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

  pub(crate) c: Vec<ScalarVector<C>>,
  c_gamma: Vec<C::F>,
}

impl<C: Ciphersuite> ArithmeticCircuitWitness<C> {
  pub fn new(
    aL: ScalarVector<C>,
    aR: ScalarVector<C>,
    v: ScalarVector<C>,
    gamma: ScalarVector<C>,
    c: Vec<ScalarVector<C>>,
    c_gamma: Vec<C::F>,
  ) -> Self {
    assert_eq!(aL.len(), aR.len());
    assert_eq!(v.len(), gamma.len());
    assert_eq!(c.len(), c_gamma.len());

    let aO = aL.mul_vec(&aR);
    ArithmeticCircuitWitness { aL, aR, aO, v, gamma, c, c_gamma }
  }
}

#[derive(Clone, Debug, Zeroize)]
pub struct ArithmeticCircuitProof<C: Ciphersuite> {
  AI: C::G,
  AO: C::G,
  S: C::G,
  T_before_ni: Vec<C::G>,
  T_after_ni: Vec<C::G>,
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
    C: PointVector<C>,
    WL: ScalarMatrix<C>,
    WR: ScalarMatrix<C>,
    WO: ScalarMatrix<C>,
    WV: ScalarMatrix<C>,
    WC: Vec<ScalarMatrix<C>>,
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
    assert_eq!(WC.len(), C.len());
    for WC in &WC {
      assert_eq!(WC.length(), q);
      // assert_eq!(WC.width(), n); TODO
    }

    assert_eq!(c.len(), q);

    Self { generators, V, C, WL, WR, WO, WV, WC, c }
  }

  fn initial_transcript(&self, transcript: &mut T) {
    transcript.domain_separate(b"arithmetic_circuit_proof");
    self.V.transcript(transcript, b"commitment");
    self.C.transcript(transcript, b"vector_commitment");
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

  fn transcript_Ts(transcript: &mut T, T_before_ni: &[C::G], T_after_ni: &[C::G]) -> C::F {
    for Ti in T_before_ni {
      transcript.append_message(b"Ti", Ti.to_bytes());
    }
    for Ti in T_after_ni {
      transcript.append_message(b"Tni+1+i", Ti.to_bytes());
    }

    let x = C::hash_to_F(b"arithmetic_circuit_proof", transcript.challenge(b"x").as_ref());
    if bool::from(x.is_zero()) {
      panic!("zero challenge in arithmetic circuit proof");
    }
    x
  }

  pub fn prove<R: RngCore + CryptoRng>(
    mut self,
    rng: &mut R,
    transcript: &mut T,
    mut witness: ArithmeticCircuitWitness<C>,
  ) -> ArithmeticCircuitProof<C> {
    let m = self.V.len();
    let n = witness.aL.len();
    assert_eq!(self.WL.width(), n);
    let q = self.WL.length();

    let mut largest_WC = 0;
    for WC in &self.WC {
      largest_WC = largest_WC.max(WC.width());
    }
    // TODO: Move into Statement::new
    let n = n.max(largest_WC);
    self.WL.width = n;
    self.WR.width = n;
    self.WO.width = n;
    for WC in &mut self.WC {
      WC.width = n;
    }
    while witness.aL.len() < n {
      witness.aL.0.push(C::F::ZERO);
      witness.aR.0.push(C::F::ZERO);
      witness.aO.0.push(C::F::ZERO);
    }

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

    let nc = self.C.len();

    // TODO: Have this modified n' formula signed off on
    let ni = 2 + (2 * (nc + 1).div_ceil(2));
    let ilr = ni / 2;
    let io = ni;
    let is = ni + 1;
    let jlr = ni / 2;
    let jo = 0;
    let js = ni + 1;

    let mut ik = Vec::with_capacity(nc);
    assert!(nc <= (ni / 2));
    for i in 0 .. nc {
      ik.push(i);
    }
    /*
    {
      let mut all_is = ik.clone();
      all_is.push(ilr);
      all_is.push(io);
      all_is.push(is);
      assert_eq!(all_is.iter().collect::<std::collections::HashSet<_>>().len(), all_is.len());
    }
    */
    let mut jk = Vec::with_capacity(nc);
    assert!((ni - nc) >= (ni / 2));
    for i in 0 .. nc {
      jk.push(ni - i);
    }
    /*
    {
      let mut all_js = jk.clone();
      all_js.push(jlr);
      all_js.push(jo);
      all_js.push(js);
      assert_eq!(all_js.iter().collect::<std::collections::HashSet<_>>().len(), all_js.len());
    }
    */

    let coefficients = ni + 1;
    let total_terms = 1 + coefficients;
    let mut l = Vec::with_capacity(total_terms);
    while l.len() < total_terms {
      l.push(ScalarVector::new(witness.aL.len()));
    }
    l[ilr] = witness.aL.add_vec(&inv_y.mul_vec(&self.WR.mul_vec(&z)));
    l[io] = witness.aO.clone();
    l[is] = ScalarVector(sL);
    for (i, c) in ik.iter().zip(witness.c.clone().into_iter()) {
      assert_eq!(l[*i], ScalarVector::new(witness.aL.len()));
      l[*i] = c;
      while l[*i].len() < n {
        l[*i].0.push(C::F::ZERO);
      }
    }

    let mut r = Vec::with_capacity(total_terms);
    while r.len() < total_terms {
      r.push(ScalarVector::new(witness.aL.len()));
    }
    r[jlr] = self.WL.mul_vec(&z).add_vec(&y.mul_vec(&witness.aR));
    r[jo] = self.WO.mul_vec(&z).sub_vec(&y);
    r[js] = y.mul_vec(&ScalarVector(sR.clone()));
    for (j, WC) in jk.iter().zip(self.WC.iter()) {
      assert_eq!(r[*j], ScalarVector::new(witness.aL.len()));
      r[*j] = WC.mul_vec(&z);
    }

    let poly_eval = |poly: &[ScalarVector<C>], X: C::F| -> ScalarVector<_> {
      let mut res = ScalarVector::<C>::new(poly[0].0.len());
      for coeff in poly.iter().rev() {
        res = res.mul(X);
        res = res.add_vec(&coeff);
      }
      res
    };

    let mut t = vec![C::F::ZERO; 1 + (2 * (l.len() - 1))];
    for (i, l) in l.iter().enumerate() {
      for (j, r) in r.iter().enumerate() {
        let new_coeff = i + j;
        t[new_coeff] += l.inner_product(&r);
      }
    }

    /*
    let w = self
      .WL
      .mul_vec(&witness.aL)
      .add_vec(&self.WR.mul_vec(&witness.aR))
      .add_vec(&self.WO.mul_vec(&witness.aO));
    */

    {
      let dummy_X = C::F::random(&mut *rng);
      let mut res = C::F::ZERO;
      for coeff in t.iter().rev() {
        res *= dummy_X;
        res += coeff;
      }
      assert_eq!(poly_eval(&l, dummy_X).inner_product(&poly_eval(&r, dummy_X)), res);
    }

    /*
    let t2 = witness.aL.inner_product(&witness.aR.mul_vec(&y)) - witness.aO.inner_product(&y) +
      z.inner_product(&w) +
      delta;
    */

    let mut tau_before_ni = vec![];
    for _ in 0 .. ni {
      tau_before_ni.push(C::F::random(&mut *rng));
    }
    let mut tau_after_ni = vec![];
    for _ in 0 .. t[(ni + 1) ..].len() {
      tau_after_ni.push(C::F::random(&mut *rng));
    }
    let mut T_before_ni = vec![];
    for (t, tau) in t[.. ni].iter().zip(tau_before_ni.iter()) {
      T_before_ni
        .push(multiexp(&[(*t, self.generators.g().point()), (*tau, self.generators.h().point())]));
    }
    let mut T_after_ni = vec![];
    for (t, tau) in t[(ni + 1) ..].iter().zip(tau_after_ni.iter()) {
      T_after_ni
        .push(multiexp(&[(*t, self.generators.g().point()), (*tau, self.generators.h().point())]));
    }

    let x = Self::transcript_Ts(transcript, &T_before_ni, &T_after_ni);
    let l = poly_eval(&l, x);
    let r = poly_eval(&r, x);

    {
      assert_eq!(l.len(), r.len());
      let mut found_pow_2 = false;
      let mut l_len = l.len();
      for _ in 0 .. 64 {
        if l_len == 1 {
          found_pow_2 = true;
          break;
        }
        l_len >>= 1;
      }
      assert!(found_pow_2);
    }

    let mut tau_poly = vec![];
    tau_poly.extend(tau_before_ni);
    tau_poly.push(self.WV.mul_vec(&z).inner_product(&witness.gamma));
    tau_poly.extend(tau_after_ni);
    let mut tau_x = {
      let mut res = C::F::ZERO;
      for coeff in tau_poly.iter().rev() {
        res *= x;
        res += coeff;
      }
      res
    };

    let mut x_ilr = C::F::ONE;
    for _ in 0 .. ilr {
      x_ilr *= x;
    }
    let mut x_io = C::F::ONE;
    for _ in 0 .. io {
      x_io *= x;
    }
    let mut x_is = C::F::ONE;
    for _ in 0 .. is {
      x_is *= x;
    }

    let mut u = (alpha * x_ilr) + (beta * x_io) + (p * x_is);
    let mut c_gamma_x = C::F::ONE;
    for c_gamma in &witness.c_gamma {
      u += c_gamma_x * c_gamma;
      c_gamma_x *= x;
    }

    ArithmeticCircuitProof { AI, AO, S, T_before_ni, T_after_ni, tau_x, u, l: l.0, r: r.0 }
  }

  pub fn verify<R: RngCore + CryptoRng>(
    mut self,
    rng: &mut R,
    verifier: &mut BatchVerifier<(), C::G>,
    transcript: &mut T,
    proof: ArithmeticCircuitProof<C>,
  ) {
    let nc = self.C.len();
    let ni = 2 + (2 * (nc + 1).div_ceil(2));
    let l_r_poly_len = 1 + ni + 1;
    let m = self.V.len();
    let n = self.WL.width();
    let q = self.WL.length();
    assert_eq!(proof.l.len(), proof.r.len());
    let t_poly_len = (2 * l_r_poly_len) - 1;
    assert_eq!(proof.T_before_ni.len(), ni);
    assert_eq!(proof.T_after_ni.len(), t_poly_len - ni - 1);

    let mut largest_WC = 0;
    for WC in &self.WC {
      largest_WC = largest_WC.max(WC.width());
    }
    // TODO: Move into Statement::new
    let n = n.max(largest_WC);
    assert_eq!(proof.l.len(), n);
    self.WL.width = n;
    self.WR.width = n;
    self.WO.width = n;
    for WC in &mut self.WC {
      WC.width = n;
    }
    self.initial_transcript(transcript);
    let (y, inv_y, z) = Self::transcript_AI_AO_S(transcript, proof.AI, proof.AO, proof.S, n, q);
    let delta = inv_y.mul_vec(&self.WR.mul_vec(&z)).inner_product(&self.WL.mul_vec(&z));

    let x = Self::transcript_Ts(transcript, &proof.T_before_ni, &proof.T_after_ni);

    let reduced = self.generators.reduce(n);
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
    let mut current_x = C::F::ONE;
    let t_poly_len = (2 * l_r_poly_len) - 1;
    let mut Ts = C::G::identity();
    for Ti in &proof.T_before_ni {
      Ts += *Ti * current_x;
      current_x *= x;
    }
    let x_ni = current_x;
    current_x *= x;
    for Ti in &proof.T_after_ni {
      Ts += *Ti * current_x;
      current_x *= x;
    }

    let mut Cs = C::G::identity();
    let mut C_x_coeff = C::F::ONE;
    for C in &self.C.0 {
      Cs += *C * C_x_coeff;
      C_x_coeff *= x;
    }

    // TODO: Queue this as a batch verification statement
    assert!(bool::from(
      (multiexp_vartime(&[
        (t_caret - (x_ni * (delta + z.inner_product(&self.c))), reduced.g().point()),
        (proof.tau_x, reduced.h().point()),
      ]) - self.V.mul_vec(&self.WV.mul_vec(&z).mul(x_ni)).sum() -
        Ts)
        .is_identity()
    ));

    let mut x_ilr = C::F::ONE;
    for _ in 0 .. (ni / 2) {
      x_ilr *= x;
    }

    let mut WCs = C::G::identity();
    for (j, WC) in self.WC.iter().enumerate() {
      let j = ni - j;
      let mut x_coeff = C::F::ONE;
      for _ in 0 .. j {
        x_coeff *= x;
      }
      WCs += hi.mul_vec(&WC.mul_vec(&z)).sum() * x_coeff;
    }

    // h' ** y is equivalent to h as h' is h ** inv_y
    // TOOD: Cache this as a long lived generator
    let mut h_sum = reduced.generator(GeneratorsList::HBold1, 0).point();
    for i in 1 .. n {
      h_sum += reduced.generator(GeneratorsList::HBold1, i).point();
    }
    let mut P_terms = vec![
      (C::F::ONE, WO.sum() - h_sum + WCs + Cs),
      (x_ilr, proof.AI + WL.sum() + WR.sum()),
      (x_ni, proof.AO),
      (x_ni * x, proof.S),
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
