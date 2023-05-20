use rand_core::{RngCore, OsRng};

use transcript::{Transcript, RecommendedTranscript};
use ciphersuite::{group::ff::Field, Ciphersuite, Ristretto, Pallas, Vesta};

use crate::{
  RANGE_PROOF_BITS, BulletproofsCurve, RangeCommitment,
  aggregate_range_proof::{AggregateRangeStatement, AggregateRangeWitness},
  tests::generators,
};

fn test_aggregate_range_proof<C: BulletproofsCurve>(runs: usize) {
  for m in 1 ..= runs {
    let (g_bold, h_bold, _, _) = generators(RANGE_PROOF_BITS * m);

    let mut commitments = vec![];
    for _ in 0 .. m {
      commitments
        .push(RangeCommitment::new(OsRng.next_u64(), <C as Ciphersuite>::F::random(&mut OsRng)));
    }
    let statement = AggregateRangeStatement::<C>::new(
      g_bold,
      h_bold,
      commitments.iter().map(RangeCommitment::calculate).collect(),
    );
    let witness = AggregateRangeWitness::<C>::new(&commitments);

    let mut transcript = RecommendedTranscript::new(b"Aggregate Range Proof Test");
    let proof = statement.clone().prove(&mut OsRng, &mut transcript.clone(), witness);
    statement.verify(&mut transcript, proof);
  }
}

#[test]
fn test_aggregate_range_proof_ristretto() {
  test_aggregate_range_proof::<Ristretto>(16);
}

// Uses less runs for pallas/vesta due to performance under debug
#[test]
fn test_aggregate_range_proof_pallas() {
  test_aggregate_range_proof::<Pallas>(16);
}

#[test]
fn test_aggregate_range_proof_vesta() {
  test_aggregate_range_proof::<Vesta>(16);
}
