use rand_core::OsRng;

use transcript::{Transcript, RecommendedTranscript};
use ciphersuite::{
  group::{ff::Field, Group},
  Ciphersuite, Ristretto,
};

use crate::{
  BulletproofsCurve, ScalarVector, ScalarMatrix, PointVector,
  arithmetic_circuit_proof::{ArithmeticCircuitStatement, ArithmeticCircuitWitness},
};

type Generators =
  (PointVector<Ristretto>, PointVector<Ristretto>, PointVector<Ristretto>, PointVector<Ristretto>);

fn generators(n: usize) -> Generators {
  let gens = || {
    let mut res = PointVector::<Ristretto>::new(n);
    for i in 0 .. n {
      res[i] = <Ristretto as Ciphersuite>::G::random(&mut OsRng);
    }
    res
  };
  (gens(), gens(), gens(), gens())
}

#[test]
fn test_zero_arithmetic_circuit() {
  let (g_bold1, g_bold2, h_bold1, h_bold2) = generators(1);

  let value = <Ristretto as Ciphersuite>::F::random(&mut OsRng);
  let gamma = <Ristretto as Ciphersuite>::F::random(&mut OsRng);
  let commitment =
    (<Ristretto as Ciphersuite>::generator() * value) + (Ristretto::alt_generator() * gamma);
  let V = PointVector(vec![commitment]);

  let zero_vec = || ScalarVector::<Ristretto>(vec![<Ristretto as Ciphersuite>::F::ZERO]);

  let aL = zero_vec();
  let aR = zero_vec();

  let WL = ScalarMatrix(vec![zero_vec()]);
  let WR = ScalarMatrix(vec![zero_vec()]);
  let WO = ScalarMatrix(vec![zero_vec()]);
  let WV = ScalarMatrix(vec![zero_vec()]);
  let c = zero_vec();

  let statement = ArithmeticCircuitStatement::<Ristretto>::new(
    g_bold1, g_bold2, h_bold1, h_bold2, V, WL, WR, WO, WV, c,
  );
  let witness = ArithmeticCircuitWitness::<Ristretto>::new(
    aL,
    aR,
    ScalarVector(vec![value]),
    ScalarVector(vec![gamma]),
  );

  let mut transcript = RecommendedTranscript::new(b"Zero Circuit Test");
  let proof = statement.clone().prove(&mut OsRng, &mut transcript.clone(), witness);
  statement.verify(&mut transcript, proof);
}

#[test]
fn test_multiplication_arithmetic_circuit() {
  let m = 4; // Input secrets
  let n = 1; // Multiplications
  let q = 5; // Constraints

  // Hand-written circuit for:
  // Commitmnts x, y, z, z1
  // y = 2x
  // x * y = z
  // z + 1 = z1

  let (g_bold1, g_bold2, h_bold1, h_bold2) = generators(n);

  let commit = |value, gamma| {
    (<Ristretto as Ciphersuite>::generator() * value) + (Ristretto::alt_generator() * gamma)
  };

  let x = <Ristretto as Ciphersuite>::F::random(&mut OsRng);
  let x_mask = <Ristretto as Ciphersuite>::F::random(&mut OsRng);
  let x_commitment = commit(x, x_mask);

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

  let aL = ScalarVector::<Ristretto>(vec![x]);
  let aR = ScalarVector::<Ristretto>(vec![y]);

  let WL = ScalarMatrix(vec![
    ScalarVector(vec![<Ristretto as Ciphersuite>::F::ONE]),
    ScalarVector(vec![<Ristretto as Ciphersuite>::F::ZERO]),
    ScalarVector(vec![<Ristretto as Ciphersuite>::F::ZERO]),
    ScalarVector(vec![<Ristretto as Ciphersuite>::F::ZERO]),
    ScalarVector(vec![<Ristretto as Ciphersuite>::F::ZERO]),
  ]);
  let WR = ScalarMatrix(vec![
    ScalarVector(vec![<Ristretto as Ciphersuite>::F::ZERO]),
    ScalarVector(vec![<Ristretto as Ciphersuite>::F::ONE]),
    ScalarVector(vec![<Ristretto as Ciphersuite>::F::ZERO]),
    ScalarVector(vec![<Ristretto as Ciphersuite>::F::ZERO]),
    ScalarVector(vec![<Ristretto as Ciphersuite>::F::ONE]),
  ]);
  let WO = ScalarMatrix(vec![
    ScalarVector(vec![<Ristretto as Ciphersuite>::F::ZERO]),
    ScalarVector(vec![<Ristretto as Ciphersuite>::F::ZERO]),
    ScalarVector(vec![<Ristretto as Ciphersuite>::F::ONE]),
    ScalarVector(vec![<Ristretto as Ciphersuite>::F::ONE]),
    ScalarVector(vec![<Ristretto as Ciphersuite>::F::ZERO]),
  ]);
  let WV = ScalarMatrix(vec![
    // Constrain inputs
    ScalarVector(vec![
      <Ristretto as Ciphersuite>::F::ONE,
      <Ristretto as Ciphersuite>::F::ZERO,
      <Ristretto as Ciphersuite>::F::ZERO,
      <Ristretto as Ciphersuite>::F::ZERO,
    ]),
    ScalarVector(vec![
      <Ristretto as Ciphersuite>::F::ZERO,
      <Ristretto as Ciphersuite>::F::ONE,
      <Ristretto as Ciphersuite>::F::ZERO,
      <Ristretto as Ciphersuite>::F::ZERO,
    ]),
    // Confirm the multiplication
    ScalarVector(vec![
      <Ristretto as Ciphersuite>::F::ZERO,
      <Ristretto as Ciphersuite>::F::ZERO,
      <Ristretto as Ciphersuite>::F::ONE,
      <Ristretto as Ciphersuite>::F::ZERO,
    ]),
    // Verify the next commitment is output + 1
    ScalarVector(vec![
      <Ristretto as Ciphersuite>::F::ZERO,
      <Ristretto as Ciphersuite>::F::ZERO,
      <Ristretto as Ciphersuite>::F::ZERO,
      <Ristretto as Ciphersuite>::F::ONE,
    ]),
    // Verify y is 2x
    ScalarVector(vec![
      <Ristretto as Ciphersuite>::F::from(2u64),
      <Ristretto as Ciphersuite>::F::ZERO,
      <Ristretto as Ciphersuite>::F::ZERO,
      <Ristretto as Ciphersuite>::F::ZERO,
    ]),
  ]);
  let c = ScalarVector::<Ristretto>(vec![
    <Ristretto as Ciphersuite>::F::ZERO,
    <Ristretto as Ciphersuite>::F::ZERO,
    <Ristretto as Ciphersuite>::F::ZERO,
    <Ristretto as Ciphersuite>::F::ONE,
    <Ristretto as Ciphersuite>::F::ZERO,
  ]);

  let statement = ArithmeticCircuitStatement::<Ristretto>::new(
    g_bold1, g_bold2, h_bold1, h_bold2, V, WL, WR, WO, WV, c,
  );
  let witness = ArithmeticCircuitWitness::<Ristretto>::new(
    aL,
    aR,
    ScalarVector(vec![x, y, z, z1]),
    ScalarVector(vec![x_mask, y_mask, z_mask, z1_mask]),
  );

  let mut transcript = RecommendedTranscript::new(b"Multiplication Circuit Test");
  let proof = statement.clone().prove(&mut OsRng, &mut transcript.clone(), witness);
  statement.verify(&mut transcript, proof);
}
