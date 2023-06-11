// The inner product relation is P = sum(g_bold * a, h_bold * b, g * (a * y * b), h * alpha)

use rand_core::OsRng;

use transcript::{Transcript, RecommendedTranscript};

use multiexp::BatchVerifier;
use ciphersuite::{
  group::{ff::Field, Group},
  Ciphersuite, Ristretto,
};

use crate::{
  ScalarVector,
  weighted_inner_product::{WipStatement, WipWitness},
  weighted_inner_product,
  tests::generators,
};

#[test]
fn test_zero_weighted_inner_product() {
  let P = <Ristretto as Ciphersuite>::G::identity();
  let y = <Ristretto as Ciphersuite>::F::random(&mut OsRng);

  let statement = WipStatement::<_, Ristretto>::new(generators(1).reduce(1, false), P, y);
  let witness = WipWitness::<Ristretto>::new(
    ScalarVector::<Ristretto>::new(1),
    ScalarVector::<Ristretto>::new(1),
    <Ristretto as Ciphersuite>::F::ZERO,
  );

  let mut transcript = RecommendedTranscript::new(b"Zero WIP Test");
  let proof = statement.clone().prove(&mut OsRng, &mut transcript.clone(), witness);

  let mut verifier = BatchVerifier::new(1);
  statement.verify(&mut OsRng, &mut verifier, &mut transcript, proof);
  assert!(verifier.verify_vartime());
}

#[test]
fn test_weighted_inner_product() {
  // P = sum(g_bold * a, h_bold * b, g * (a * y * b), h * alpha)
  let mut verifier = BatchVerifier::new(6);
  let generators = generators(32);
  for i in [1, 2, 4, 8, 16, 32] {
    let generators = generators.clone().reduce(i, false);
    let (g, h, g_bold, h_bold) = generators.clone().decompose();

    let mut a = ScalarVector::<Ristretto>::new(i);
    let mut b = ScalarVector::<Ristretto>::new(i);
    let alpha = <Ristretto as Ciphersuite>::F::random(&mut OsRng);

    let y = <Ristretto as Ciphersuite>::F::random(&mut OsRng);
    let mut y_vec = ScalarVector::new(g_bold.len());
    y_vec[0] = y;
    for i in 1 .. y_vec.len() {
      y_vec[i] = y_vec[i - 1] * y;
    }

    for i in 0 .. i {
      a[i] = <Ristretto as Ciphersuite>::F::random(&mut OsRng);
      b[i] = <Ristretto as Ciphersuite>::F::random(&mut OsRng);
    }

    let P = g_bold.multiexp(&a) +
      h_bold.multiexp(&b) +
      (g * weighted_inner_product(&a, &b, &y_vec)) +
      (h * alpha);

    let statement = WipStatement::<_, Ristretto>::new(generators, P, y);
    let witness = WipWitness::<Ristretto>::new(a, b, alpha);

    let mut transcript = RecommendedTranscript::new(b"WIP Test");
    let proof = statement.clone().prove(&mut OsRng, &mut transcript.clone(), witness);
    statement.verify(&mut OsRng, &mut verifier, &mut transcript, proof);
  }
  assert!(verifier.verify_vartime());
}
