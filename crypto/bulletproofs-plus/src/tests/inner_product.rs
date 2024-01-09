// The inner product relation is P = sum(g_bold * a, h_bold * b, g * (a * b))

use rand_core::OsRng;

use transcript::{Transcript, RecommendedTranscript};

use multiexp::BatchVerifier;
use ciphersuite::{
  group::{ff::Field, Group},
  Ciphersuite, Ristretto,
};

use crate::{
  ScalarVector, PointVector, GeneratorsList,
  inner_product::{IpStatement, IpWitness},
  tests::generators,
};

#[test]
fn test_zero_inner_product() {
  let P = <Ristretto as Ciphersuite>::G::identity();

  let generators = generators(1);
  let reduced = generators.per_proof().reduce(1, false);
  let statement = IpStatement::<_, Ristretto, _>::new(&reduced, P);
  let witness = IpWitness::<Ristretto>::new(
    ScalarVector::<Ristretto>::new(1),
    ScalarVector::<Ristretto>::new(1),
  );

  let mut transcript = RecommendedTranscript::new(b"Zero IP Test");
  let proof = statement.clone().prove(&mut OsRng, &mut transcript.clone(), witness);

  let mut verifier = BatchVerifier::new(1);
  statement.verify(&mut OsRng, &mut verifier, &mut transcript, proof);
  assert!(verifier.verify_vartime());
}

#[test]
fn test_inner_product() {
  // P = sum(g_bold * a, h_bold * b, g * (a * b))
  let mut verifier = BatchVerifier::new(6);
  let generators = generators(32);
  for i in [1, 2, 4, 8, 16, 32] {
    let generators = generators.per_proof().reduce(i, false);
    let g = generators.g().point();
    assert_eq!(generators.len(), i);
    let mut g_bold = vec![];
    let mut h_bold = vec![];
    for i in 0 .. i {
      g_bold.push(generators.generator(GeneratorsList::GBold1, i).point());
      h_bold.push(generators.generator(GeneratorsList::HBold1, i).point());
    }
    let g_bold = PointVector(g_bold);
    let h_bold = PointVector(h_bold);

    let mut a = ScalarVector::<Ristretto>::new(i);
    let mut b = ScalarVector::<Ristretto>::new(i);

    for i in 0 .. i {
      a[i] = <Ristretto as Ciphersuite>::F::random(&mut OsRng);
      b[i] = <Ristretto as Ciphersuite>::F::random(&mut OsRng);
    }

    let P = g_bold.multiexp(&a) + h_bold.multiexp(&b) + (g * a.inner_product(&b));

    let statement = IpStatement::<_, Ristretto, _>::new(&generators, P);
    let witness = IpWitness::<Ristretto>::new(a, b);

    let mut transcript = RecommendedTranscript::new(b"IP Test");
    let proof = statement.clone().prove(&mut OsRng, &mut transcript.clone(), witness);
    statement.verify(&mut OsRng, &mut verifier, &mut transcript, proof);
  }
  assert!(verifier.verify_vartime());
}
