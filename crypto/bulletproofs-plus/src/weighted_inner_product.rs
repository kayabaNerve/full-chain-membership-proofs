use rand_core::{RngCore, CryptoRng};

use zeroize::{Zeroize, ZeroizeOnDrop};

use transcript::Transcript;

use multiexp::{multiexp, multiexp_vartime, Point as MultiexpPoint, BatchVerifier};
use ciphersuite::{
  group::{
    ff::{Field, PrimeField},
    GroupEncoding,
  },
  Ciphersuite,
};

use crate::{ScalarVector, PointVector, Generators, weighted_inner_product};

#[derive(Clone, PartialEq, Eq, Debug, Zeroize)]
enum P<C: Ciphersuite> {
  Point(C::G),
  Terms(Vec<(C::F, MultiexpPoint<C::G>)>),
}

// Figure 1
#[derive(Clone, Debug, Zeroize)]
pub struct WipStatement<T: Transcript, C: Ciphersuite> {
  generators: Generators<T, C>,
  P: P<C>,
  y: ScalarVector<C>,
}

#[derive(Clone, Debug, Zeroize, ZeroizeOnDrop)]
pub struct WipWitness<C: Ciphersuite> {
  a: ScalarVector<C>,
  b: ScalarVector<C>,
  alpha: C::F,
}

impl<C: Ciphersuite> WipWitness<C> {
  pub fn new(a: ScalarVector<C>, b: ScalarVector<C>, alpha: C::F) -> Self {
    assert!(!a.0.is_empty());
    assert_eq!(a.len(), b.len());
    Self { a, b, alpha }
  }
}

#[derive(Clone)]
struct TrackedScalarVector<C: Ciphersuite> {
  raw: Vec<C::F>,
  positions: Vec<Vec<usize>>,
}

#[derive(Clone, PartialEq, Eq, Debug, Zeroize)]
pub struct WipProof<C: Ciphersuite> {
  L: Vec<C::G>,
  R: Vec<C::G>,
  A: C::G,
  B: C::G,
  r_answer: C::F,
  s_answer: C::F,
  delta_answer: C::F,
}

impl<T: Transcript, C: Ciphersuite> WipStatement<T, C> {
  pub fn new(generators: Generators<T, C>, P: C::G, y: C::F) -> Self {
    // y ** n
    let mut y_vec = ScalarVector::new(generators.g_bold1.len());
    y_vec[0] = y;
    for i in 1 .. y_vec.len() {
      y_vec[i] = y_vec[i - 1] * y;
    }

    Self { generators, P: P::Point(P), y: y_vec }
  }

  pub(crate) fn new_without_P_transcript(
    generators: Generators<T, C>,
    P: Vec<(C::F, MultiexpPoint<C::G>)>,
    y: ScalarVector<C>,
  ) -> Self {
    Self { generators, P: P::Terms(P), y }
  }

  fn initial_transcript(&mut self, transcript: &mut T) {
    transcript.domain_separate(b"weighted_inner_product");
    transcript.append_message(b"generators", self.generators.transcript.challenge(b"summary"));
    if let P::Point(P) = &self.P {
      transcript.append_message(b"P", P.to_bytes());
    }
    transcript.append_message(b"y", self.y[0].to_repr());
  }

  fn transcript_L_R(transcript: &mut T, L: C::G, R: C::G) -> C::F {
    transcript.append_message(b"L", L.to_bytes());
    transcript.append_message(b"R", R.to_bytes());

    let e = C::hash_to_F(b"weighted_inner_product", transcript.challenge(b"e").as_ref());
    if bool::from(e.is_zero()) {
      panic!("zero challenge in WIP round");
    }
    e
  }

  fn transcript_A_B(transcript: &mut T, A: C::G, B: C::G) -> C::F {
    transcript.append_message(b"A", A.to_bytes());
    transcript.append_message(b"B", B.to_bytes());

    let e = C::hash_to_F(b"weighted_inner_product", transcript.challenge(b"e").as_ref());
    if bool::from(e.is_zero()) {
      panic!("zero challenge in final WIP round");
    }
    e
  }

  // Prover's variant of the shared code block to calculate G/H/P when n > 1
  // Returns each permutation of G/H since the prover needs to do operation on each permutation
  // P is dropped as it's unused in the prover's path
  // TODO: It'd still probably be faster to keep in terms of the original generators, both between
  // the reduced amount of group operations and the potential tabling of the generators under
  // multiexp
  fn next_G_H(
    transcript: &mut T,
    mut g_bold1: PointVector<C>,
    mut g_bold2: PointVector<C>,
    mut h_bold1: PointVector<C>,
    mut h_bold2: PointVector<C>,
    L: C::G,
    R: C::G,
    y_inv_n_hat: C::F,
  ) -> (C::F, C::F, C::F, C::F, PointVector<C>, PointVector<C>) {
    assert_eq!(g_bold1.len(), g_bold2.len());
    assert_eq!(h_bold1.len(), h_bold2.len());
    assert_eq!(g_bold1.len(), h_bold1.len());

    let e = Self::transcript_L_R(transcript, L, R);
    let inv_e = e.invert().unwrap();

    // This vartime is safe as all of these arguments are public
    let mut new_g_bold = Vec::with_capacity(g_bold1.len());
    let e_y_inv = e * y_inv_n_hat;
    for g_bold in g_bold1.0.drain(..).zip(g_bold2.0.drain(..)) {
      new_g_bold.push(multiexp_vartime(&[(inv_e, g_bold.0), (e_y_inv, g_bold.1)]));
    }

    let mut new_h_bold = Vec::with_capacity(h_bold1.len());
    for h_bold in h_bold1.0.drain(..).zip(h_bold2.0.drain(..)) {
      new_h_bold.push(multiexp_vartime(&[(e, h_bold.0), (inv_e, h_bold.1)]));
    }

    let e_square = e.square();
    let inv_e_square = inv_e.square();

    (e, inv_e, e_square, inv_e_square, PointVector(new_g_bold), PointVector(new_h_bold))
  }

  // TODO: This is O(n log n). It should be feasible to make O(n) (specifically 2n)
  fn next_G_H_P_without_permutation(
    transcript: &mut T,
    g_bold: &mut TrackedScalarVector<C>,
    h_bold: &mut TrackedScalarVector<C>,
    P_terms: &mut Vec<(C::F, MultiexpPoint<C::G>)>,
    L: C::G,
    R: C::G,
    y_inv_n_hat: C::F,
  ) {
    assert_eq!(g_bold.positions.len(), h_bold.positions.len());
    if (g_bold.positions.len() % 2) == 1 {
      g_bold.positions.push(vec![]);
    }
    if (h_bold.positions.len() % 2) == 1 {
      h_bold.positions.push(vec![]);
    }

    let e = Self::transcript_L_R(transcript, L, R);
    // TODO: Create all e challenges, then use a batch inversion
    let inv_e = e.invert().unwrap();

    let e_y_inv = e * y_inv_n_hat;

    let section_len = g_bold.positions.len() / 2;
    let scale_section = |generators: &mut TrackedScalarVector<C>, section, scalar| {
      for s in (section * section_len) .. ((section + 1) * section_len) {
        for pos in &generators.positions[s] {
          let pos: &usize = pos;
          generators.raw[*pos] *= scalar;
        }
      }
    };
    // g_bold1
    scale_section(g_bold, 0, inv_e);
    // g_bold2
    scale_section(g_bold, 1, e_y_inv);
    // h_bold1
    scale_section(h_bold, 0, e);
    // h_bold2
    scale_section(h_bold, 1, inv_e);

    // Now merge their positions
    let merge_positions = |generators: &mut TrackedScalarVector<_>| {
      let high = generators.positions.len() / 2;
      for i in 1 ..= high {
        let mut popped = generators.positions.pop().unwrap();
        generators.positions[high - i].append(&mut popped);
      }
      assert_eq!(generators.positions.len(), high);
    };
    merge_positions(g_bold);
    merge_positions(h_bold);

    let e_square = e.square();
    let inv_e_square = inv_e.square();
    P_terms.push((e_square, MultiexpPoint::Variable(L)));
    P_terms.push((inv_e_square, MultiexpPoint::Variable(R)));
  }

  pub fn prove<R: RngCore + CryptoRng>(
    mut self,
    rng: &mut R,
    transcript: &mut T,
    witness: WipWitness<C>,
  ) -> WipProof<C> {
    self.initial_transcript(transcript);

    let WipStatement { generators, P, mut y } = self;
    let (g, h, mut g_bold, mut h_bold) = generators.decompose();

    // Check P has the expected relationship
    if let P::Point(P) = &P {
      let mut P_terms = witness
        .a
        .0
        .iter()
        .copied()
        .zip(g_bold.0.iter().copied())
        .chain(witness.b.0.iter().copied().zip(h_bold.0.iter().copied()))
        .collect::<Vec<_>>();
      P_terms.push((weighted_inner_product(&witness.a, &witness.b, &y), g));
      P_terms.push((witness.alpha, h));
      debug_assert_eq!(multiexp(&P_terms), *P);
      P_terms.zeroize();
    }

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
      let (g_bold1, g_bold2) = g_bold.split();
      let (h_bold1, h_bold2) = h_bold.split();

      let n_hat = g_bold1.len();
      assert_eq!(a1.len(), n_hat);
      assert_eq!(a2.len(), n_hat);
      assert_eq!(b1.len(), n_hat);
      assert_eq!(b2.len(), n_hat);
      assert_eq!(g_bold1.len(), n_hat);
      assert_eq!(g_bold2.len(), n_hat);
      assert_eq!(h_bold1.len(), n_hat);
      assert_eq!(h_bold2.len(), n_hat);

      let y_n_hat = y[n_hat - 1];
      y.0.truncate(n_hat);

      let d_l = C::F::random(&mut *rng);
      let d_r = C::F::random(&mut *rng);

      let c_l = weighted_inner_product(&a1, &b2, &y);
      let c_r = weighted_inner_product(&(a2.mul(y_n_hat)), &b1, &y);

      // TODO: Calculate these with a batch inversion
      let y_inv_n_hat = y_n_hat.invert().unwrap();

      let mut L_terms = a1
        .mul(y_inv_n_hat)
        .0
        .drain(..)
        .zip(g_bold2.0.iter().copied())
        .chain(b2.0.iter().copied().zip(h_bold1.0.iter().copied()))
        .collect::<Vec<_>>();
      L_terms.push((c_l, g));
      L_terms.push((d_l, h));
      let L = multiexp(&L_terms);
      L_vec.push(L);
      L_terms.zeroize();

      let mut R_terms = a2
        .mul(y_n_hat)
        .0
        .drain(..)
        .zip(g_bold1.0.iter().copied())
        .chain(b1.0.iter().copied().zip(h_bold2.0.iter().copied()))
        .collect::<Vec<_>>();
      R_terms.push((c_r, g));
      R_terms.push((d_r, h));
      let R = multiexp(&R_terms);
      R_vec.push(R);
      R_terms.zeroize();

      let (e, inv_e, e_square, inv_e_square);
      (e, inv_e, e_square, inv_e_square, g_bold, h_bold) =
        Self::next_G_H(transcript, g_bold1, g_bold2, h_bold1, h_bold2, L, R, y_inv_n_hat);

      a = a1.mul(e).add_vec(&a2.mul(y_n_hat * inv_e));
      b = b1.mul(inv_e).add_vec(&b2.mul(e));
      alpha += (d_l * e_square) + (d_r * inv_e_square);

      debug_assert_eq!(g_bold.len(), a.len());
      debug_assert_eq!(g_bold.len(), h_bold.len());
      debug_assert_eq!(g_bold.len(), b.len());
    }

    // n == 1 case from figure 1
    assert_eq!(g_bold.len(), 1);
    assert_eq!(h_bold.len(), 1);

    assert_eq!(a.len(), 1);
    assert_eq!(b.len(), 1);

    let r = C::F::random(&mut *rng);
    let s = C::F::random(&mut *rng);
    let delta = C::F::random(&mut *rng);
    let long_n = C::F::random(&mut *rng);

    let ry = r * y[0];

    let mut A_terms =
      vec![(r, g_bold[0]), (s, h_bold[0]), ((ry * b[0]) + (s * y[0] * a[0]), g), (delta, h)];
    let A = multiexp(&A_terms);
    A_terms.zeroize();

    let mut B_terms = vec![(ry * s, g), (long_n, h)];
    let B = multiexp(&B_terms);
    B_terms.zeroize();

    let e = Self::transcript_A_B(transcript, A, B);

    let r_answer = r + (a[0] * e);
    let s_answer = s + (b[0] * e);
    let delta_answer = long_n + (delta * e) + (alpha * e.square());

    WipProof { L: L_vec, R: R_vec, A, B, r_answer, s_answer, delta_answer }
  }

  pub fn verify<R: RngCore + CryptoRng>(
    mut self,
    rng: &mut R,
    verifier: &mut BatchVerifier<(), C::G>,
    transcript: &mut T,
    proof: WipProof<C>,
  ) {
    self.initial_transcript(transcript);

    let WipStatement { generators, P, y } = self;
    let (g, h, mut g_bold, mut h_bold) = generators.multiexp_decompose();

    assert!(!g_bold.is_empty());
    assert_eq!(g_bold.len(), h_bold.len());

    let mut tracked_g_bold = TrackedScalarVector::<C> {
      raw: vec![C::F::ONE; g_bold.len() + (g_bold.len() % 2)],
      positions: (0 .. g_bold.len()).map(|i| vec![i]).collect(),
    };
    let mut tracked_h_bold = tracked_g_bold.clone();

    // Verify the L/R lengths
    {
      let mut lr_len = 0;
      while (1 << lr_len) < g_bold.len() {
        lr_len += 1;
      }
      assert_eq!(proof.L.len(), lr_len);
      assert_eq!(proof.R.len(), lr_len);
    }

    let mut P_terms = match P {
      P::Point(point) => vec![(C::F::ONE, MultiexpPoint::Variable(point))],
      P::Terms(terms) => terms,
    };
    P_terms.reserve(6 + g_bold.len() + h_bold.len() + proof.L.len());
    for (L, R) in proof.L.iter().zip(proof.R.iter()) {
      let n_hat = (tracked_g_bold.positions.len() + (tracked_g_bold.positions.len() % 2)) / 2;
      let y_n_hat = y[n_hat - 1];
      // TODO: Take these in from the caller
      let y_inv_n_hat = y_n_hat.invert().unwrap();

      Self::next_G_H_P_without_permutation(
        transcript,
        &mut tracked_g_bold,
        &mut tracked_h_bold,
        &mut P_terms,
        *L,
        *R,
        y_inv_n_hat,
      );
    }

    let e = Self::transcript_A_B(transcript, proof.A, proof.B);
    let neg_e_square = -e.square();

    let mut multiexp = P_terms;
    for (scalar, _) in multiexp.iter_mut() {
      *scalar *= neg_e_square;
    }

    let re = proof.r_answer * e;
    for (i, point) in g_bold.drain(..).enumerate() {
      multiexp.push((tracked_g_bold.raw[i] * re, point));
    }

    let se = proof.s_answer * e;
    for (i, point) in h_bold.drain(..).enumerate() {
      multiexp.push((tracked_h_bold.raw[i] * se, point));
    }

    multiexp.push((-e, MultiexpPoint::Variable(proof.A)));
    multiexp.push((proof.r_answer * y[0] * proof.s_answer, g));
    multiexp.push((proof.delta_answer, h));
    multiexp.push((-C::F::ONE, MultiexpPoint::Variable(proof.B)));

    verifier.queue(rng, (), multiexp);
  }
}
