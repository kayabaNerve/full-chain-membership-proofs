use rand_core::{RngCore, OsRng};

use transcript::{Transcript, RecommendedTranscript};

use ciphersuite::{group::Group, Ciphersuite, Pallas, Ristretto};

use bulletproofs_plus::RangeCommitment;

use crate::{Statement, Witness};

#[test]
fn test() {
  let value = OsRng.next_u64();
  let c1 = RangeCommitment::<Pallas>::masking(&mut OsRng, value);
  let c2 = RangeCommitment::<Ristretto>::masking(&mut OsRng, value);

  let h1 = <Pallas as Ciphersuite>::G::random(&mut OsRng);
  let h2 = <Ristretto as Ciphersuite>::G::random(&mut OsRng);

  let statement = Statement::new(
    Pallas::generator(),
    h1,
    Ristretto::generator(),
    h2,
    c1.calculate(Pallas::generator(), h1),
    c2.calculate(Ristretto::generator(), h2),
  );

  let mut transcript = RecommendedTranscript::new(b"COPZ Cross-Group DLEq Proof Test");
  let proof = statement.clone().prove(&mut OsRng, &mut transcript.clone(), Witness::new(c1, c2));
  statement.verify(&mut transcript, proof);
}
