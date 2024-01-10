use rand_core::OsRng;

use transcript::{Transcript, RecommendedTranscript};

use multiexp::BatchVerifier;
use ciphersuite::{group::ff::Field, Ciphersuite, Ristretto};

use crate::{
  ScalarVector, ScalarMatrix, PointVector, GeneratorsList,
  arithmetic_circuit_proof::{ArithmeticCircuitStatement, ArithmeticCircuitWitness},
  tests::generators,
};

#[test]
fn test_zero_arithmetic_circuit() {
  let generators = generators(1);

  let value = <Ristretto as Ciphersuite>::F::random(&mut OsRng);
  let gamma = <Ristretto as Ciphersuite>::F::random(&mut OsRng);
  let commitment = (generators.g().point() * value) + (generators.h().point() * gamma);
  let V = PointVector(vec![commitment]);

  let zero_vec = || ScalarVector::<Ristretto>(vec![<Ristretto as Ciphersuite>::F::ZERO]);

  let aL = zero_vec();
  let aR = zero_vec();

  let mut WL = ScalarMatrix::new(1);
  WL.push(vec![(0, <Ristretto as Ciphersuite>::F::ZERO)]);
  let mut WR = ScalarMatrix::new(1);
  WR.push(vec![(0, <Ristretto as Ciphersuite>::F::ZERO)]);
  let mut WO = ScalarMatrix::new(1);
  WO.push(vec![(0, <Ristretto as Ciphersuite>::F::ZERO)]);
  let mut WV = ScalarMatrix::new(1);
  WV.push(vec![(0, <Ristretto as Ciphersuite>::F::ZERO)]);
  let c = zero_vec();

  let statement = ArithmeticCircuitStatement::<_, Ristretto>::new(
    generators.per_proof(),
    V,
    PointVector(vec![]),
    WL,
    WR,
    WO,
    WV,
    vec![],
    c,
  );
  let witness = ArithmeticCircuitWitness::<Ristretto>::new(
    aL,
    aR,
    ScalarVector(vec![value]),
    ScalarVector(vec![gamma]),
    vec![],
    vec![],
  );

  let mut transcript = RecommendedTranscript::new(b"Zero Circuit Test");
  let proof = statement.clone().prove(&mut OsRng, &mut transcript.clone(), witness);
  let mut verifier = BatchVerifier::new(1);
  statement.verify(&mut OsRng, &mut verifier, &mut transcript, proof);
  assert!(verifier.verify_vartime());
}

#[test]
fn test_vector_commitment_arithmetic_circuit() {
  let generators = generators(1);

  let value = <Ristretto as Ciphersuite>::F::random(&mut OsRng);
  let gamma = <Ristretto as Ciphersuite>::F::random(&mut OsRng);
  let commitment = (generators.per_proof().generator(GeneratorsList::GBold1, 0).point() * value) +
    (generators.h().point() * gamma);
  let V = PointVector(vec![]);
  let C = PointVector(vec![commitment]);

  let zero_vec = || ScalarVector::<Ristretto>(vec![<Ristretto as Ciphersuite>::F::ZERO]);

  let aL = zero_vec();
  let aR = zero_vec();

  let mut WL = ScalarMatrix::new(1);
  WL.push(vec![(0, <Ristretto as Ciphersuite>::F::ZERO)]);
  let mut WR = ScalarMatrix::new(1);
  WR.push(vec![(0, <Ristretto as Ciphersuite>::F::ZERO)]);
  let mut WO = ScalarMatrix::new(1);
  WO.push(vec![(0, <Ristretto as Ciphersuite>::F::ZERO)]);
  let mut WV = ScalarMatrix::new(0);
  WV.push(vec![]);
  let mut WC = vec![ScalarMatrix::new(1)];
  WC[0].push(vec![(0, <Ristretto as Ciphersuite>::F::ZERO)]);
  let c = zero_vec();

  let statement = ArithmeticCircuitStatement::<_, Ristretto>::new(
    generators.per_proof(),
    V,
    C,
    WL,
    WR,
    WO,
    WV,
    WC,
    c,
  );
  let witness = ArithmeticCircuitWitness::<Ristretto>::new(
    aL,
    aR,
    ScalarVector(vec![]),
    ScalarVector(vec![]),
    vec![ScalarVector(vec![value])],
    vec![gamma],
  );

  let mut transcript = RecommendedTranscript::new(b"Vector Commitment Circuit Test");
  let proof = statement.clone().prove(&mut OsRng, &mut transcript.clone(), witness);
  let mut verifier = BatchVerifier::new(1);
  statement.verify(&mut OsRng, &mut verifier, &mut transcript, proof);
  assert!(verifier.verify_vartime());
}

#[test]
fn test_multiplication_arithmetic_circuit() {
  let m = 4; // Input secrets
  let n = 1; // Multiplications
  let q = 5; // Constraints

  // Hand-written circuit for:
  // Commitments x, y, z, z1
  // x * y = z
  // z + 1 = z1

  let generators = generators(n);

  let commit = |value, gamma| (generators.g().point() * value) + (generators.h().point() * gamma);

  let x = <Ristretto as Ciphersuite>::F::random(&mut OsRng);
  let x_mask = <Ristretto as Ciphersuite>::F::random(&mut OsRng);
  let x_commitment = commit(x, x_mask);

  let x_vector_mask = <Ristretto as Ciphersuite>::F::random(&mut OsRng);
  let x_vector_commitment = (generators.per_proof().generator(GeneratorsList::GBold1, 0).point() *
    x) +
    (generators.h().point() * x_vector_mask);

  let y = x.double();
  let y_mask = <Ristretto as Ciphersuite>::F::random(&mut OsRng);
  let y_commitment = commit(y, y_mask);

  let z = x * y;
  let z_mask = <Ristretto as Ciphersuite>::F::random(&mut OsRng);
  let z_commitment = commit(z, z_mask);

  let z1 = z + <Ristretto as Ciphersuite>::F::ONE;
  let z1_mask = <Ristretto as Ciphersuite>::F::random(&mut OsRng);
  let z1_commitment = commit(z1, z1_mask);

  let V = PointVector(vec![x_commitment, y_commitment, z_commitment, z1_commitment]);
  let C = PointVector(vec![x_vector_commitment]);

  let aL = ScalarVector::<Ristretto>(vec![x]);
  let aR = ScalarVector::<Ristretto>(vec![y]);

  let mut WL = ScalarMatrix::new(n);
  WL.push(vec![(0, <Ristretto as Ciphersuite>::F::ONE)]);
  while WL.length() < q {
    WL.push(vec![]);
  }

  let mut WR = ScalarMatrix::new(n);
  WR.push(vec![]);
  WR.push(vec![(0, <Ristretto as Ciphersuite>::F::ONE)]);
  WR.push(vec![]);
  WR.push(vec![]);
  WR.push(vec![(0, <Ristretto as Ciphersuite>::F::ONE)]);

  let mut WO = ScalarMatrix::new(n);
  WO.push(vec![]);
  WO.push(vec![]);
  WO.push(vec![(0, <Ristretto as Ciphersuite>::F::ONE)]);
  WO.push(vec![(0, <Ristretto as Ciphersuite>::F::ONE)]);
  WO.push(vec![]);

  let mut WV = ScalarMatrix::new(V.0.len());
  // Constrain inputs
  WV.push(vec![(0, <Ristretto as Ciphersuite>::F::from(2u64))]);
  WV.push(vec![(1, <Ristretto as Ciphersuite>::F::ONE)]);
  // Confirm the multiplication
  WV.push(vec![(2, <Ristretto as Ciphersuite>::F::ONE)]);
  // Verify the next commitment is output + 1
  WV.push(vec![(3, <Ristretto as Ciphersuite>::F::ONE)]);
  // Verify y is 2x
  WV.push(vec![(0, <Ristretto as Ciphersuite>::F::ONE.double())]);

  let mut WC = vec![ScalarMatrix::new(C.0.len())];
  WC[0].push(vec![(0, <Ristretto as Ciphersuite>::F::ONE)]);
  WC[0].push(vec![]);
  WC[0].push(vec![]);
  WC[0].push(vec![]);
  WC[0].push(vec![]);

  let c = ScalarVector::<Ristretto>(vec![
    <Ristretto as Ciphersuite>::F::ZERO,
    <Ristretto as Ciphersuite>::F::ZERO,
    <Ristretto as Ciphersuite>::F::ZERO,
    -<Ristretto as Ciphersuite>::F::ONE,
    <Ristretto as Ciphersuite>::F::ZERO,
  ]);

  let statement = ArithmeticCircuitStatement::<_, Ristretto>::new(
    generators.per_proof(),
    V,
    C,
    WL,
    WR,
    WO,
    WV,
    WC,
    c,
  );
  let witness = ArithmeticCircuitWitness::<Ristretto>::new(
    aL,
    aR,
    ScalarVector(vec![x, y, z, z1]),
    ScalarVector(vec![x_mask, y_mask, z_mask, z1_mask]),
    vec![ScalarVector(vec![x])],
    vec![x_vector_mask],
  );

  let mut transcript = RecommendedTranscript::new(b"Multiplication Circuit Test");
  let proof = statement.clone().prove(&mut OsRng, &mut transcript.clone(), witness);
  let mut verifier = BatchVerifier::new(1);
  statement.verify(&mut OsRng, &mut verifier, &mut transcript, proof);
  assert!(verifier.verify_vartime());
}
