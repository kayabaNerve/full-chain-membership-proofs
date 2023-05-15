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

use crate::{BulletproofsCurve, ScalarVector, PointVector, weighted_inner_product};

// Figure 1
#[derive(Clone, Debug, Zeroize)]
pub struct WipStatement<C: Ciphersuite> {
  g_bold: PointVector<C>,
  h_bold: PointVector<C>,
  P: C::G,
}

#[derive(Clone, Debug, Zeroize, ZeroizeOnDrop)]
pub struct WipWitness<C: Ciphersuite> {
  a: ScalarVector<C>,
  b: ScalarVector<C>,
  alpha: C::F,
}

impl<C: BulletproofsCurve> WipWitness<C> {
  pub fn new(a: ScalarVector<C>, b: ScalarVector<C>, alpha: C::F) -> Self {
    assert!(!a.0.is_empty());
    assert_eq!(a.len(), b.len());
    Self { a, b, alpha }
  }
}

#[derive(Clone, Debug, Zeroize)]
pub struct WipProof<C: Ciphersuite> {
  L: Vec<C::G>,
  R: Vec<C::G>,
  A: C::G,
  B: C::G,
  r_answer: C::F,
  s_answer: C::F,
  delta_answer: C::F,
}

impl<C: BulletproofsCurve> WipStatement<C> {
  pub fn new(g_bold: PointVector<C>, h_bold: PointVector<C>, P: C::G) -> Self {
    assert!(!g_bold.0.is_empty());
    assert_eq!(g_bold.len(), h_bold.len());

    Self { g_bold, h_bold, P }
  }

  fn initial_transcript<T: Transcript>(transcript: &mut T) {
    transcript.domain_separate(b"weighted_inner_product");
    transcript.append_message(b"generator", C::generator().to_bytes());
    transcript.append_message(b"alt_generator", C::alt_generator().to_bytes());
  }

  fn transcript_statement<T: Transcript>(
    transcript: &mut T,
    g_bold1: &PointVector<C>,
    g_bold2: &PointVector<C>,
    h_bold1: &PointVector<C>,
    h_bold2: &PointVector<C>,
    P: C::G,
  ) {
    for g_bold in &g_bold1.0 {
      transcript.append_message(b"g_bold1", g_bold.to_bytes());
    }
    for g_bold in &g_bold2.0 {
      transcript.append_message(b"g_bold2", g_bold.to_bytes());
    }
    for h_bold in &h_bold1.0 {
      transcript.append_message(b"h_bold1", h_bold.to_bytes());
    }
    for h_bold in &h_bold2.0 {
      transcript.append_message(b"h_bold2", h_bold.to_bytes());
    }
    transcript.append_message(b"P", P.to_bytes());
  }

  fn transcript_L_R<T: Transcript>(transcript: &mut T, L: C::G, R: C::G) -> C::F {
    transcript.append_message(b"L", L.to_bytes());
    transcript.append_message(b"R", R.to_bytes());

    let e = C::hash_to_F(b"weighted_inner_product", transcript.challenge(b"e").as_ref());
    if bool::from(e.is_zero()) {
      panic!("zero challenge in WIP round");
    }
    e
  }

  fn transcript_A_B<T: Transcript>(transcript: &mut T, A: C::G, B: C::G) -> C::F {
    transcript.append_message(b"A", A.to_bytes());
    transcript.append_message(b"B", B.to_bytes());

    let e = C::hash_to_F(b"weighted_inner_product", transcript.challenge(b"e").as_ref());
    if bool::from(e.is_zero()) {
      panic!("zero challenge in final WIP round");
    }
    e
  }

  fn next_G_H_P<T: Transcript>(
    transcript: &mut T,
    g_bold1: PointVector<C>,
    g_bold2: PointVector<C>,
    h_bold1: PointVector<C>,
    h_bold2: PointVector<C>,
    mut P: C::G,
    L: C::G,
    R: C::G,
    y_inv_n_hat: C::F,
  ) -> (C::F, C::F, C::F, C::F, PointVector<C>, PointVector<C>, C::G) {
    let n = g_bold1.len() + g_bold2.len();
    assert_eq!(g_bold1.len(), g_bold2.len());
    assert_eq!(g_bold1.len(), h_bold1.len());
    assert_eq!(g_bold1.len(), h_bold2.len());

    Self::transcript_statement(transcript, &g_bold1, &g_bold2, &h_bold1, &h_bold2, P);
    let e = Self::transcript_L_R(transcript, L, R);
    let inv_e = e.invert().unwrap();

    let g_bold = g_bold1.mul(inv_e).add_vec(&g_bold2.mul(e * y_inv_n_hat));
    let h_bold = h_bold1.mul(e).add_vec(&h_bold2.mul(inv_e));
    let e_square = e.square();
    let inv_e_square = inv_e.square();
    P += (L * e_square) + (R * inv_e_square);

    (e, inv_e, e_square, inv_e_square, g_bold, h_bold, P)
  }

  pub fn prove<R: RngCore + CryptoRng, T: Transcript>(
    self,
    rng: &mut R,
    transcript: &mut T,
    witness: WipWitness<C>,
    y: C::F,
  ) -> WipProof<C> {
    // y ** n
    let mut y_vec = ScalarVector::new(self.g_bold.len());
    y_vec[0] = y;
    for i in 1 .. y_vec.len() {
      y_vec[i] = y_vec[i - 1] * y;
    }

    // Check P has the expected relationship
    assert_eq!(
      self.g_bold.mul_vec(&witness.a).sum() +
        self.h_bold.mul_vec(&witness.b).sum() +
        (C::generator() * weighted_inner_product(&witness.a, &witness.b, &y_vec)) +
        (C::alt_generator() * witness.alpha),
      self.P,
    );

    Self::initial_transcript(transcript);

    let WipStatement { mut g_bold, mut h_bold, mut P } = self;
    assert_eq!(g_bold.len(), h_bold.len());

    let mut a = witness.a.clone();
    let mut b = witness.b.clone();
    let mut alpha = witness.alpha;
    assert_eq!(a.len(), b.len());

    // From here on, g_bold.len() is used as n
    assert_eq!(g_bold.len(), a.len());

    let mut L_vec = vec![];
    let mut R_vec = vec![];

    // else n > 1 case from figure 1
    while g_bold.len() > 1 {
      let (a1, a2) = a.clone().split();
      let (b1, b2) = b.clone().split();
      let (g_bold1, g_bold2) = g_bold.clone().split();
      let (h_bold1, h_bold2) = h_bold.clone().split();

      let n_hat = g_bold1.len();
      assert_eq!(a1.len(), n_hat);
      assert_eq!(a2.len(), n_hat);
      assert_eq!(b1.len(), n_hat);
      assert_eq!(b2.len(), n_hat);
      assert_eq!(g_bold1.len(), n_hat);
      assert_eq!(g_bold2.len(), n_hat);
      assert_eq!(h_bold1.len(), n_hat);
      assert_eq!(h_bold2.len(), n_hat);

      let y_n_hat = y_vec[n_hat - 1];
      debug_assert_eq!(y_n_hat, y.pow([u64::try_from(n_hat).unwrap()]));

      let d_l = C::F::random(&mut *rng);
      let d_r = C::F::random(&mut *rng);

      let c_l = weighted_inner_product(&a1, &b2, &y_vec);
      let c_r = weighted_inner_product(&(a2.mul(y_n_hat)), &b1, &y_vec);

      let y_inv_n_hat = y_n_hat.invert().unwrap();

      // TODO: Use a multiexp here
      #[rustfmt::skip]
      let L = g_bold2.mul_vec(&a1.mul(y_inv_n_hat)).sum() +
        h_bold1.mul_vec(&b2).sum() +
        (C::generator() * c_l) +
        (C::alt_generator() * d_l);
      L_vec.push(L);

      // TODO: Use a multiexp here too
      #[rustfmt::skip]
      let R = g_bold1.mul_vec(&a2.mul(y_n_hat)).sum() +
        h_bold2.mul_vec(&b1).sum() +
        (C::generator() * c_r) +
        (C::alt_generator() * d_r);
      R_vec.push(R);

      let (e, inv_e, e_square, inv_e_square, P_hat);
      (e, inv_e, e_square, inv_e_square, g_bold, h_bold, P_hat) =
        Self::next_G_H_P(transcript, g_bold1, g_bold2, h_bold1, h_bold2, P, L, R, y_inv_n_hat);

      debug_assert_eq!(e.invert().unwrap(), inv_e);
      debug_assert_eq!(e.square(), e_square);
      debug_assert_eq!(e_square.invert().unwrap(), inv_e_square);

      debug_assert_eq!(P_hat, (L * e_square) + P + (R * inv_e_square));
      P = P_hat;

      a = a1.mul(e).add_vec(&a2.mul(y_n_hat * inv_e));
      b = b1.mul(inv_e).add_vec(&b2.mul(e));
      alpha += (d_l * e_square) + (d_r * inv_e_square);

      debug_assert_eq!(g_bold.len(), a.len());
      debug_assert_eq!(g_bold.len(), h_bold.len());
      debug_assert_eq!(g_bold.len(), b.len());
      let alt_P = g_bold.mul_vec(&a).sum() +
        h_bold.mul_vec(&b).sum() +
        (C::generator() * weighted_inner_product(&a, &b, &y_vec)) +
        (C::alt_generator() * alpha);
      debug_assert_eq!(alt_P, P);
    }

    // n == 1 case from figure 1
    assert_eq!(g_bold.len(), 1);
    assert_eq!(h_bold.len(), 1);

    assert_eq!(a.len(), 1);
    assert_eq!(b.len(), 1);

    Self::transcript_statement(
      transcript,
      &g_bold,
      &PointVector::new(0),
      &h_bold,
      &PointVector::new(0),
      P,
    );

    let r = C::F::random(&mut *rng);
    let s = C::F::random(&mut *rng);
    let delta = C::F::random(&mut *rng);
    let long_n = C::F::random(&mut *rng);

    let ry = r * y;
    // TODO: Use a multiexp here
    #[rustfmt::skip]
    let A = (g_bold[0] * r) +
      (h_bold[0] * s) +
      (C::generator() * ((ry * b[0]) + (s * y * a[0]))) +
      (C::alt_generator() * delta);
    // TODO: Use a multiexp here too
    let B = (C::generator() * (ry * s)) + (C::alt_generator() * long_n);

    let e = Self::transcript_A_B(transcript, A, B);

    let r_answer = r + (a[0] * e);
    let s_answer = s + (b[0] * e);
    let delta_answer = long_n + (delta * e) + (alpha * e.square());

    WipProof { L: L_vec, R: R_vec, A, B, r_answer, s_answer, delta_answer }
  }

  // TODO: Use a BatchVerifier
  pub fn verify<T: Transcript>(self, transcript: &mut T, proof: WipProof<C>, y: C::F) {
    Self::initial_transcript(transcript);

    let WipStatement { mut g_bold, mut h_bold, mut P } = self;

    assert!(!g_bold.0.is_empty());
    assert_eq!(g_bold.len(), h_bold.len());

    // Verify the L/R lengths
    {
      let mut lr_len = 0;
      while (1 << lr_len) < g_bold.len() {
        lr_len += 1;
      }
      assert_eq!(proof.L.len(), lr_len);
      assert_eq!(proof.R.len(), lr_len);
    }

    // TODO: Make a common function for this
    // y ** n
    let mut y_vec = ScalarVector::<C>::new(g_bold.len());
    y_vec[0] = y;
    for i in 1 .. y_vec.len() {
      y_vec[i] = y_vec[i - 1] * y;
    }

    for (L, R) in proof.L.iter().zip(proof.R.iter()) {
      let (_e, _inv_e, _e_square, _inv_e_square);
      let (g_bold1, g_bold2) = g_bold.split();
      let (h_bold1, h_bold2) = h_bold.split();

      let n_hat = g_bold1.len();
      let y_n_hat = y_vec[n_hat - 1];
      let y_inv_n_hat = y_n_hat.invert().unwrap();

      (_e, _inv_e, _e_square, _inv_e_square, g_bold, h_bold, P) =
        Self::next_G_H_P(transcript, g_bold1, g_bold2, h_bold1, h_bold2, P, *L, *R, y_inv_n_hat);
    }
    assert_eq!(g_bold.len(), 1);
    assert_eq!(h_bold.len(), 1);

    Self::transcript_statement(
      transcript,
      &g_bold,
      &PointVector::new(0),
      &h_bold,
      &PointVector::new(0),
      P,
    );

    let e = Self::transcript_A_B(transcript, proof.A, proof.B);
    assert_eq!(
      (P * e.square()) + (proof.A * e) + proof.B,
      (g_bold[0] * (proof.r_answer * e)) +
        (h_bold[0] * (proof.s_answer * e)) +
        (C::generator() * (proof.r_answer * y * proof.s_answer)) +
        (C::alt_generator() * proof.delta_answer)
    );
  }
}
