use rand_core::{RngCore, OsRng};

use transcript::{Transcript, RecommendedTranscript};
use ciphersuite::{
  group::{ff::Field, Group},
  Ciphersuite, Ristretto,
};

use crate::{
  RANGE_PROOF_BITS, PointVector, Commitment,
  single_range_proof::{SingleRangeStatement, SingleRangeWitness},
};

#[test]
fn test_single_range_proof() {
  let mut g_bold = PointVector::<Ristretto>::new(RANGE_PROOF_BITS);
  let mut h_bold = PointVector::<Ristretto>::new(RANGE_PROOF_BITS);
  for i in 0 .. RANGE_PROOF_BITS {
    g_bold[i] = <Ristretto as Ciphersuite>::G::random(&mut OsRng);
    h_bold[i] = <Ristretto as Ciphersuite>::G::random(&mut OsRng);
  }

  let commitment =
    Commitment::new(OsRng.next_u64(), <Ristretto as Ciphersuite>::F::random(&mut OsRng));
  let statement = SingleRangeStatement::<Ristretto>::new(g_bold, h_bold, commitment.calculate());
  let witness = SingleRangeWitness::<Ristretto>::new(commitment);

  let mut transcript = RecommendedTranscript::new(b"Single Range Proof Test");
  let proof = statement.clone().prove(&mut OsRng, &mut transcript.clone(), witness);
  statement.verify(&mut transcript, proof);
}
