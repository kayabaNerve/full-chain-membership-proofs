// The inner product relation is P = sum(g_bold * a, h_bold * b, g * (a * y * b), h * alpha)

use rand_core::OsRng;

use transcript::{Transcript, RecommendedTranscript};

use multiexp::BatchVerifier;
use ciphersuite::{
  group::{ff::Field, Group},
  Ciphersuite, Ristretto,
};

use crate::{
  ScalarVector, PointVector,
  weighted_inner_product::{WipStatement, WipWitness},
  weighted_inner_product,
  tests::generators,
};

#[test]
fn test_zero_weighted_inner_product() {
  let P = <Ristretto as Ciphersuite>::G::identity();
  let g_bold = PointVector::<Ristretto>::new(1);
  let h_bold = PointVector::<Ristretto>::new(1);

  let statement = WipStatement::<Ristretto>::new(
    <Ristretto as Ciphersuite>::G::identity(),
    <Ristretto as Ciphersuite>::G::identity(),
    g_bold,
    h_bold,
    P,
  );
  let witness = WipWitness::<Ristretto>::new(
    ScalarVector::<Ristretto>::new(1),
    ScalarVector::<Ristretto>::new(1),
    <Ristretto as Ciphersuite>::F::ZERO,
  );

  let mut transcript = RecommendedTranscript::new(b"Zero WIP Test");
  let y = <Ristretto as Ciphersuite>::F::random(&mut OsRng);
  let proof = statement.clone().prove(&mut OsRng, &mut transcript.clone(), witness, y);

  let mut verifier = BatchVerifier::new(1);
  statement.verify(&mut OsRng, &mut verifier, &mut transcript, proof, y);
  assert!(verifier.verify_vartime());
}

#[test]
fn test_weighted_inner_product() {
  // P = sum(g_bold * a, h_bold * b, g * (a * y * b), h * alpha)
  for i in [1, 2, 4, 8, 16, 32] {
    let (g, h, g_bold, h_bold, _, _) = generators(i);

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

    let P = g_bold.mul_vec(&a).0.iter().sum::<<Ristretto as Ciphersuite>::G>() +
      h_bold.mul_vec(&b).0.iter().sum::<<Ristretto as Ciphersuite>::G>() +
      (g * weighted_inner_product(&a, &b, &y_vec)) +
      (h * alpha);

    let statement = WipStatement::<Ristretto>::new(g, h, g_bold, h_bold, P);
    let witness = WipWitness::<Ristretto>::new(a, b, alpha);

    let mut transcript = RecommendedTranscript::new(b"WIP Test");
    let proof = statement.clone().prove(&mut OsRng, &mut transcript.clone(), witness, y);
    let mut verifier = BatchVerifier::new(1);
    statement.verify(&mut OsRng, &mut verifier, &mut transcript, proof, y);
    assert!(verifier.verify_vartime());
  }
}
