use rand_core::{RngCore, OsRng};

use transcript::{Transcript, RecommendedTranscript};
use ciphersuite::{
  group::{ff::Field, Group},
  Ciphersuite, Ristretto,
};

use crate::{
  BulletproofsCurve, ScalarVector, PointVector, Commitment,
  single_range_proof::{SingleRangeStatement, SingleRangeWitness},
};

#[test]
fn test_single_range_proof() {
  let mut g_bold = PointVector::<Ristretto>::new(64);
  let mut h_bold = PointVector::<Ristretto>::new(64);
  for i in 0 .. 64 {
    g_bold[i] = <Ristretto as Ciphersuite>::G::random(&mut OsRng);
    h_bold[i] = <Ristretto as Ciphersuite>::G::random(&mut OsRng);
  }

  let commitment =
    Commitment::new(<Ristretto as Ciphersuite>::F::random(&mut OsRng), OsRng.next_u64());
  let statement = SingleRangeStatement::<Ristretto>::new(g_bold, h_bold, commitment.calculate());
  let witness = SingleRangeWitness::<Ristretto>::new(commitment);

  let mut transcript = RecommendedTranscript::new(b"Single Range Proof Test");
  let proof = statement.clone().prove(&mut OsRng, &mut transcript.clone(), witness);
  statement.verify(&mut transcript, proof);
}
