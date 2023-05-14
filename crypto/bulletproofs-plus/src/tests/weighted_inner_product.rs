// The inner product relation is P = sum(g_bold * a, h_bold * b, g * (a * y * b), h * alpha)

use rand_core::OsRng;

use transcript::{Transcript, RecommendedTranscript};
use ciphersuite::{
  group::{ff::Field, Group},
  Ciphersuite, Ristretto,
};

use crate::{
  BulletproofsCurve, ScalarVector, PointVector,
  weighted_inner_product::{WipStatement, WipWitness},
  weighted_inner_product,
};

impl BulletproofsCurve for Ristretto {
  fn alt_generator() -> <Self as Ciphersuite>::G {
    <Ristretto as Ciphersuite>::generator() *
      <Ristretto as Ciphersuite>::hash_to_F(b"alt_generator", &[]) // TODO
  }
  fn alt_generators() -> &'static [<Self as Ciphersuite>::G] {
    todo!()
  }
}

#[test]
fn test_zero_weighted_inner_product() {
  let P = <Ristretto as Ciphersuite>::G::identity();
  let g_bold = PointVector::<Ristretto>::new(1);
  let h_bold = PointVector::<Ristretto>::new(1);

  let statement = WipStatement::<Ristretto>::new(g_bold, h_bold, P);
  let witness = WipWitness::<Ristretto>::new(
    ScalarVector::<Ristretto>::new(1),
    ScalarVector::<Ristretto>::new(1),
    <Ristretto as Ciphersuite>::F::ZERO,
  );

  let mut transcript = RecommendedTranscript::new(b"Zero WIP Test");
  let y = <Ristretto as Ciphersuite>::F::random(&mut OsRng);
  let proof = statement.clone().prove(&mut OsRng, &mut transcript.clone(), witness, y);

  statement.verify(&mut transcript, proof, y);
}

#[test]
fn test_weighted_inner_product() {
  // P = sum(g_bold * a, h_bold * b, g * (a * y * b), h * alpha)
  for i in [1, 2, 4, 8, 16, 32] {
    dbg!(i);

    let mut g_bold = PointVector::<Ristretto>::new(i);
    let mut h_bold = PointVector::<Ristretto>::new(i);

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
      g_bold[i] = <Ristretto as Ciphersuite>::G::random(&mut OsRng);
      h_bold[i] = <Ristretto as Ciphersuite>::G::random(&mut OsRng);
      a[i] = <Ristretto as Ciphersuite>::F::random(&mut OsRng);
      b[i] = <Ristretto as Ciphersuite>::F::random(&mut OsRng);
    }

    let P = g_bold.mul_vec(&a).0.iter().sum::<<Ristretto as Ciphersuite>::G>() +
      h_bold.mul_vec(&b).0.iter().sum::<<Ristretto as Ciphersuite>::G>() +
      (Ristretto::generator() * weighted_inner_product(&a, &b, &y_vec)) +
      Ristretto::alt_generator() * alpha;

    let statement = WipStatement::<Ristretto>::new(g_bold, h_bold, P);
    let witness = WipWitness::<Ristretto>::new(a, b, alpha);

    let mut transcript = RecommendedTranscript::new(b"WIP Test");
    let proof = statement.clone().prove(&mut OsRng, &mut transcript.clone(), witness, y);
    statement.verify(&mut transcript, proof, y);
  }
}
