use rand_core::{RngCore, OsRng};

use transcript::{Transcript, RecommendedTranscript};
use ciphersuite::{
  group::{ff::Field, Group},
  Ciphersuite, Ristretto, Pallas, Vesta,
};

use crate::{
  RANGE_PROOF_BITS, PointVector, RangeCommitment,
  aggregate_range_proof::{AggregateRangeStatement, AggregateRangeWitness},
};

fn test_aggregate_range_proof<C: Ciphersuite>() {
  for m in 1 ..= 16 {
    let mut g_bold = PointVector::<Ristretto>::new(RANGE_PROOF_BITS * m);
    let mut h_bold = PointVector::<Ristretto>::new(RANGE_PROOF_BITS * m);
    for i in 0 .. (RANGE_PROOF_BITS * m) {
      g_bold[i] = <Ristretto as Ciphersuite>::G::random(&mut OsRng);
      h_bold[i] = <Ristretto as Ciphersuite>::G::random(&mut OsRng);
    }

    let mut commitments = vec![];
    for _ in 0 .. m {
      commitments.push(RangeCommitment::new(
        OsRng.next_u64(),
        <Ristretto as Ciphersuite>::F::random(&mut OsRng),
      ));
    }
    let statement = AggregateRangeStatement::<Ristretto>::new(
      g_bold,
      h_bold,
      commitments.iter().map(RangeCommitment::calculate).collect(),
    );
    let witness = AggregateRangeWitness::<Ristretto>::new(&commitments);

    let mut transcript = RecommendedTranscript::new(b"Aggregate Range Proof Test");
    let proof = statement.clone().prove(&mut OsRng, &mut transcript.clone(), witness);
    statement.verify(&mut transcript, proof);
  }
}

#[test]
fn test_aggregate_range_proof_ristretto() {
  test_aggregate_range_proof::<Ristretto>();
}

#[test]
fn test_aggregate_range_proof_pallas() {
  test_aggregate_range_proof::<Pallas>();
}

#[test]
fn test_aggregate_range_proof_vesta() {
  test_aggregate_range_proof::<Vesta>();
}
