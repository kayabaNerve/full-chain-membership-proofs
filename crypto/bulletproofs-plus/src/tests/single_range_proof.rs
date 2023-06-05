use rand_core::{RngCore, OsRng};

use transcript::{Transcript, RecommendedTranscript};

use multiexp::BatchVerifier;
use ciphersuite::{group::ff::Field, Ciphersuite, Ristretto};

use crate::{
  RANGE_PROOF_BITS, RangeCommitment,
  single_range_proof::{SingleRangeStatement, SingleRangeWitness},
  tests::generators,
};

#[test]
fn test_single_range_proof() {
  let (g, h, g_bold, h_bold, _, _) = generators(RANGE_PROOF_BITS);

  let commitment =
    RangeCommitment::new(OsRng.next_u64(), <Ristretto as Ciphersuite>::F::random(&mut OsRng));
  let statement =
    SingleRangeStatement::<Ristretto>::new(g, h, g_bold, h_bold, commitment.calculate(g, h));
  let witness = SingleRangeWitness::<Ristretto>::new(commitment);

  let mut transcript = RecommendedTranscript::new(b"Single Range Proof Test");
  let proof = statement.clone().prove(&mut OsRng, &mut transcript.clone(), witness);
  let mut verifier = BatchVerifier::new(1);
  statement.verify(&mut OsRng, &mut verifier, &mut transcript, proof);
  assert!(verifier.verify_vartime());
}
