use rand_core::{RngCore, OsRng};

use transcript::{Transcript, RecommendedTranscript};

use multiexp::BatchVerifier;
use ciphersuite::{
  group::{ff::Field, Group},
  Ciphersuite, Pallas, Vesta,
};

use ecip::Ecip;
use bulletproofs_plus::{
  arithmetic_circuit::Circuit, gadgets::elliptic_curve::DLogTable,
  tests::generators as generators_fn,
};

use crate::{
  CurveCycle, permissible::Permissible, tree::Tree, tests::Pasta, new_blind, membership_gadget,
};

#[test]
fn test_membership() {
  let pallas_generators = generators_fn::<Pallas>(512 * 4);
  let pallas_h = pallas_generators.h();

  let vesta_generators = generators_fn::<Vesta>(512 * 4);
  let vesta_h = vesta_generators.h();

  let permissible_c1 = Permissible::<<Pasta as CurveCycle>::C1> {
    h: pallas_h,
    alpha: <<Pasta as CurveCycle>::C1 as Ecip>::FieldElement::random(&mut OsRng),
    beta: <<Pasta as CurveCycle>::C1 as Ecip>::FieldElement::random(&mut OsRng),
  };
  let permissible_c2 = Permissible::<<Pasta as CurveCycle>::C2> {
    h: vesta_h,
    alpha: <<Pasta as CurveCycle>::C2 as Ecip>::FieldElement::random(&mut OsRng),
    beta: <<Pasta as CurveCycle>::C2 as Ecip>::FieldElement::random(&mut OsRng),
  };
  let leaf_randomness = <<Pasta as CurveCycle>::C1 as Ciphersuite>::G::random(&mut OsRng);

  let mut verifier_c1 = BatchVerifier::new(3 + (3 * 4));
  let mut verifier_c2 = BatchVerifier::new(3 + (3 * 4));

  // Test with various widths
  for width in 2 ..= 4usize {
    let max = u64::try_from(width).unwrap().pow(4);
    let mut tree = Tree::<Pasta>::new(permissible_c1, permissible_c2, leaf_randomness, width, max);

    // Create a full tree
    let mut leaves = vec![];
    for _ in 0 .. max {
      leaves.push(<<Pasta as CurveCycle>::C1 as Ciphersuite>::G::random(&mut OsRng));
    }
    tree.add_leaves(&leaves);
    for leaf in leaves.iter_mut() {
      while !permissible_c1.point(*leaf) {
        *leaf += leaf_randomness;
      }
    }

    let blind_c1 =
      new_blind::<_, Pallas, Vesta>(&mut OsRng, DLogTable::<Pallas>::new(pallas_h).trits(), 0).0;
    let point = leaves[usize::try_from(OsRng.next_u64() % (1 << 30)).unwrap() % leaves.len()];
    assert!(permissible_c1.point(point));
    let blinded_point = point - (pallas_generators.h() * blind_c1);

    let gadget = |circuit_c1: &mut Circuit<_, Pallas>, circuit_c2: &mut Circuit<_, Vesta>| {
      membership_gadget::<_, _, Pasta>(
        &mut OsRng,
        circuit_c1,
        circuit_c2,
        &tree,
        blinded_point,
        Some(blind_c1).filter(|_| circuit_c1.prover()),
      );
    };

    let mut transcript = RecommendedTranscript::new(b"Membership Gadget Test");

    let mut circuit_c1 = Circuit::new(pallas_generators.clone(), true, None);
    let mut circuit_c2 = Circuit::new(vesta_generators.clone(), true, None);
    gadget(&mut circuit_c1, &mut circuit_c2);

    let mut prove_transcript = transcript.clone();
    let (_, pallas_commitments, pallas_proof, pallas_proofs) =
      circuit_c1.prove_with_vector_commitments(&mut OsRng, &mut prove_transcript);
    let (_, vesta_commitments, vesta_proof, vesta_proofs) =
      circuit_c2.prove_with_vector_commitments(&mut OsRng, &mut prove_transcript);

    let mut circuit_c1 = Circuit::new(pallas_generators.clone(), false, Some(pallas_commitments));
    let mut circuit_c2 = Circuit::new(vesta_generators.clone(), false, Some(vesta_commitments));
    gadget(&mut circuit_c1, &mut circuit_c2);

    circuit_c1.verify_with_vector_commitments(
      &mut OsRng,
      &mut verifier_c1,
      &mut transcript,
      pallas_proof,
      pallas_proofs,
    );
    circuit_c2.verify_with_vector_commitments(
      &mut OsRng,
      &mut verifier_c2,
      &mut transcript,
      vesta_proof,
      vesta_proofs,
    );
  }

  assert!(verifier_c1.verify_vartime());
  assert!(verifier_c2.verify_vartime());
}
