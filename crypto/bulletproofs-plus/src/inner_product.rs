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

use crate::{ScalarVector, PointVector, GeneratorsList, InnerProductGenerators, padded_pow_of_2};

#[derive(Clone, PartialEq, Eq, Debug, Zeroize)]
enum P<C: Ciphersuite> {
  Point(C::G),
  Terms(Vec<(C::F, MultiexpPoint<C::G>)>),
}

// Protocol 2
#[derive(Clone, Debug)]
pub struct IpStatement<
  'a,
  T: 'static + Transcript,
  C: Ciphersuite,
  GB: Clone + AsRef<[MultiexpPoint<C::G>]>,
> {
  generators: &'a InnerProductGenerators<'a, T, C, GB>,
  P: P<C>,
}

impl<'a, T: 'static + Transcript, C: Ciphersuite, GB: Clone + AsRef<[MultiexpPoint<C::G>]>> Zeroize
  for IpStatement<'a, T, C, GB>
{
  fn zeroize(&mut self) {
    self.P.zeroize();
  }
}

#[derive(Clone, Debug, Zeroize, ZeroizeOnDrop)]
pub struct IpWitness<C: Ciphersuite> {
  a: ScalarVector<C>,
  b: ScalarVector<C>,
}

impl<C: Ciphersuite> IpWitness<C> {
  pub fn new(mut a: ScalarVector<C>, mut b: ScalarVector<C>) -> Self {
    assert!(!a.0.is_empty());
    assert_eq!(a.len(), b.len());

    // Pad to the nearest power of 2
    let missing = padded_pow_of_2(a.len()) - a.len();
    a.0.reserve(missing);
    b.0.reserve(missing);
    for _ in 0 .. missing {
      a.0.push(C::F::ZERO);
      b.0.push(C::F::ZERO);
    }

    Self { a, b }
  }
}

#[derive(Clone, PartialEq, Eq, Debug, Zeroize)]
pub struct IpProof<C: Ciphersuite> {
  L: Vec<C::G>,
  R: Vec<C::G>,
  a: C::F,
  b: C::F,
}

impl<'a, T: 'static + Transcript, C: Ciphersuite, GB: 'a + Clone + AsRef<[MultiexpPoint<C::G>]>>
  IpStatement<'a, T, C, GB>
{
  pub fn new(generators: &'a InnerProductGenerators<'a, T, C, GB>, P: C::G) -> Self {
    debug_assert_eq!(generators.len(), padded_pow_of_2(generators.len()));
    Self { generators, P: P::Point(P) }
  }

  pub(crate) fn new_without_P_transcript(
    generators: &'a InnerProductGenerators<'a, T, C, GB>,
    P: Vec<(C::F, MultiexpPoint<C::G>)>,
  ) -> Self {
    debug_assert_eq!(generators.len(), padded_pow_of_2(generators.len()));
    Self { generators, P: P::Terms(P) }
  }

  fn initial_transcript(&mut self, transcript: &mut T) {
    transcript.domain_separate(b"inner_product");
    transcript
      .append_message(b"generators", self.generators.transcript.clone().challenge(b"summary"));
    if let P::Point(P) = &self.P {
      transcript.append_message(b"P", P.to_bytes());
    }
  }

  fn transcript_L_R(transcript: &mut T, L: C::G, R: C::G) -> C::F {
    transcript.append_message(b"L", L.to_bytes());
    transcript.append_message(b"R", R.to_bytes());

    let x = C::hash_to_F(b"inner_product", transcript.challenge(b"x").as_ref());
    if bool::from(x.is_zero()) {
      panic!("zero challenge in IP round");
    }
    x
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
  ) -> (C::F, C::F, PointVector<C>, PointVector<C>) {
    assert_eq!(g_bold1.len(), g_bold2.len());
    assert_eq!(h_bold1.len(), h_bold2.len());
    assert_eq!(g_bold1.len(), h_bold1.len());

    let x = Self::transcript_L_R(transcript, L, R);
    let inv_x = x.invert().unwrap();

    // This vartime is safe as all of these arguments are public
    let mut new_g_bold = Vec::with_capacity(g_bold1.len());
    for g_bold in g_bold1.0.drain(..).zip(g_bold2.0.drain(..)) {
      new_g_bold.push(multiexp_vartime(&[(inv_x, g_bold.0), (x, g_bold.1)]));
    }

    let mut new_h_bold = Vec::with_capacity(h_bold1.len());
    for h_bold in h_bold1.0.drain(..).zip(h_bold2.0.drain(..)) {
      new_h_bold.push(multiexp_vartime(&[(x, h_bold.0), (inv_x, h_bold.1)]));
    }

    let x_square = x.square();
    let inv_x_square = inv_x.square();

    (x, inv_x, PointVector(new_g_bold), PointVector(new_h_bold))
  }

  /*
  This has room for optimization worth investigating further. It currently takes
  an iterative approach. It can be optimized further via divide and conquer.

  Assume there are 4 challenges.

  Iterative approach (current):
    1. Do the optimal multiplications across challenge column 0 and 1.
    2. Do the optimal multiplications across that result and column 2.
    3. Do the optimal multiplications across that result and column 3.

  Divide and conquer (worth investigating further):
    1. Do the optimal multiplications across challenge column 0 and 1.
    2. Do the optimal multiplications across challenge column 2 and 3.
    3. Multiply both results together.

  When there are 4 challenges (n=16), the iterative approach does 28 multiplications
  versus divide and conquer's 24.
  */
  fn challenge_products(challenges: &[(C::F, C::F)]) -> Vec<C::F> {
    let mut products = vec![C::F::ONE; 1 << challenges.len()];

    if !challenges.is_empty() {
      products[0] = challenges[0].1;
      products[1] = challenges[0].0;

      for (j, challenge) in challenges.iter().enumerate().skip(1) {
        let mut slots = (1 << (j + 1)) - 1;
        while slots > 0 {
          products[slots] = products[slots / 2] * challenge.0;
          products[slots - 1] = products[slots / 2] * challenge.1;

          slots = slots.saturating_sub(2);
        }
      }

      // Sanity check since if the above failed to populate, it'd be critical
      for product in &products {
        debug_assert!(!bool::from(product.is_zero()));
      }
    }

    products
  }

  pub fn prove<R: RngCore + CryptoRng>(
    mut self,
    rng: &mut R,
    transcript: &mut T,
    witness: IpWitness<C>,
  ) -> IpProof<C> {
    self.initial_transcript(transcript);

    let IpStatement { generators, P } = self;
    let u = generators.g().point();

    assert_eq!(generators.len(), witness.a.len());
    let (g, h) = (generators.g().point(), generators.h().point());
    let mut g_bold = vec![];
    let mut h_bold = vec![];
    for i in 0 .. generators.len() {
      g_bold.push(generators.generator(GeneratorsList::GBold1, i).point());
      h_bold.push(generators.generator(GeneratorsList::HBold1, i).point());
    }
    let mut g_bold = PointVector(g_bold);
    let mut h_bold = PointVector(h_bold);

    let mut a = witness.a.clone();
    let mut b = witness.b.clone();
    assert_eq!(a.len(), b.len());

    // From here on, g_bold.len() is used as n
    assert_eq!(g_bold.len(), a.len());

    let mut L_vec = vec![];
    let mut R_vec = vec![];

    // else n > 1 case
    while g_bold.len() > 1 {
      let (a1, a2) = a.clone().split();
      let (b1, b2) = b.clone().split();

      let (g_bold1, g_bold2) = g_bold.split();
      let (h_bold1, h_bold2) = h_bold.split();

      let n_hat = g_bold1.len();
      debug_assert_eq!(a1.len(), n_hat);
      debug_assert_eq!(a2.len(), n_hat);
      debug_assert_eq!(b1.len(), n_hat);
      debug_assert_eq!(b2.len(), n_hat);
      debug_assert_eq!(g_bold1.len(), n_hat);
      debug_assert_eq!(g_bold2.len(), n_hat);
      debug_assert_eq!(h_bold1.len(), n_hat);
      debug_assert_eq!(h_bold2.len(), n_hat);

      let cl = a1.inner_product(&b2);
      let cr = a2.inner_product(&b1);

      let mut L_terms = Vec::with_capacity(1 + (2 * g_bold1.len()));
      for pair in a1
        .0
        .clone()
        .into_iter()
        .zip(g_bold2.0.clone().into_iter())
        .chain(b2.0.clone().into_iter().zip(h_bold1.0.clone().into_iter()))
      {
        L_terms.push(pair);
      }
      L_terms.push((cl, u));
      // Uses vartime since this isn't a ZK proof
      let L = multiexp_vartime(&L_terms);
      L_vec.push(L);

      let mut R_terms = Vec::with_capacity(1 + (2 * g_bold1.len()));
      for pair in a2
        .0
        .clone()
        .into_iter()
        .zip(g_bold1.0.clone().into_iter())
        .chain(b1.0.clone().into_iter().zip(h_bold2.0.clone().into_iter()))
      {
        R_terms.push(pair);
      }
      R_terms.push((cr, u));
      let R = multiexp_vartime(&R_terms);
      R_vec.push(R);

      let (x, inv_x);
      (x, inv_x, g_bold, h_bold) =
        Self::next_G_H(transcript, g_bold1, g_bold2, h_bold1, h_bold2, L, R);

      a = a1.mul(x).add_vec(&a2.mul(inv_x));
      b = b1.mul(inv_x).add_vec(&b2.mul(x));

      debug_assert_eq!(g_bold.len(), h_bold.len());
      debug_assert_eq!(g_bold.len(), a.len());
      debug_assert_eq!(g_bold.len(), b.len());
    }

    // n == 1 case from figure 1
    assert_eq!(g_bold.len(), 1);
    assert_eq!(h_bold.len(), 1);

    assert_eq!(a.len(), 1);
    assert_eq!(b.len(), 1);

    IpProof { L: L_vec, R: R_vec, a: a[0], b: b[0] }
  }

  pub fn verify<R: RngCore + CryptoRng>(
    mut self,
    rng: &mut R,
    verifier: &mut BatchVerifier<(), C::G>,
    transcript: &mut T,
    proof: IpProof<C>,
  ) {
    self.initial_transcript(transcript);

    let IpStatement { generators, P } = self;
    let u = generators.g().clone();

    // Verify the L/R lengths
    {
      let mut lr_len = 0;
      while (1 << lr_len) < generators.len() {
        lr_len += 1;
      }
      assert_eq!(proof.L.len(), lr_len);
      assert_eq!(proof.R.len(), lr_len);
      assert_eq!(generators.len(), 1 << lr_len);
    }

    let mut P_terms = match P {
      P::Point(point) => vec![(C::F::ONE, MultiexpPoint::Variable(point))],
      P::Terms(terms) => terms,
    };
    P_terms.reserve(2 * generators.len());

    let mut challenges = Vec::with_capacity(proof.L.len());
    let product_cache = {
      let mut xs = Vec::with_capacity(proof.L.len());
      for (L, R) in proof.L.iter().zip(proof.R.iter()) {
        xs.push(Self::transcript_L_R(transcript, *L, *R));
      }

      let mut inv_xs = xs.clone();
      let mut scratch = vec![C::F::ZERO; xs.len()];
      ciphersuite::group::ff::BatchInverter::invert_with_external_scratch(
        &mut inv_xs,
        &mut scratch,
      );
      drop(scratch);

      assert_eq!(xs.len(), inv_xs.len());
      assert_eq!(xs.len(), proof.L.len());
      assert_eq!(xs.len(), proof.R.len());
      for ((x, inv_x), (L, R)) in
        xs.drain(..).zip(inv_xs.drain(..)).zip(proof.L.iter().zip(proof.R.iter()))
      {
        challenges.push((x, inv_x));

        let x_square = x.square();
        let inv_x_square = inv_x.square();
        P_terms.push((x_square, MultiexpPoint::Variable(*L)));
        P_terms.push((inv_x_square, MultiexpPoint::Variable(*R)));
      }

      Self::challenge_products(&challenges)
    };

    let c = proof.a * proof.b;

    let mut multiexp = P_terms;
    multiexp.reserve(1 + (2 * generators.len()));

    for i in 0 .. generators.len() {
      // TODO: Have BatchVerifier take &MultiexpPoint
      multiexp.push((
        -(product_cache[i] * proof.a),
        generators.generator(GeneratorsList::GBold1, i).clone(),
      ));
    }
    for i in 0 .. generators.len() {
      multiexp.push((
        -(product_cache[product_cache.len() - 1 - i] * proof.b),
        generators.generator(GeneratorsList::HBold1, i).clone(),
      ));
    }
    multiexp.push((-c, u));

    verifier.queue(rng, (), multiexp);
  }
}
