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
  CurveCycle,
  permissible::Permissible,
  tree::{Hash, Tree},
  tests::Pasta,
  new_blind, membership_gadget,
};

#[ignore]
#[test]
fn bench_membership() {
  let generators = std::time::Instant::now();
  let mut pallas_generators = generators_fn::<Pallas>(512 * 4);
  let pallas_h = pallas_generators.h().point();

  let mut vesta_generators = generators_fn::<Vesta>(512 * 4);
  let vesta_h = vesta_generators.h().point();

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

  let width = 2u64.pow(4u32);
  dbg!(width);
  let depth = 4u32;
  dbg!(depth);
  let max = width.pow(depth);
  let mut tree = Tree::<RecommendedTranscript, Pasta>::new(
    permissible_c1,
    permissible_c2,
    leaf_randomness,
    usize::try_from(width).unwrap(),
    max,
  );
  tree.whitelist_vector_commitments(&mut pallas_generators, &mut vesta_generators);
  dbg!(std::time::Instant::now() - generators);

  // Create a full tree
  let tree_time = std::time::Instant::now();
  let max = usize::try_from(max).unwrap();
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
  dbg!(std::time::Instant::now() - tree_time);

  let transcript = RecommendedTranscript::new(b"Membership Gadget Test");
  let gadget = |transcript: &mut RecommendedTranscript, circuit_c1: &mut Circuit<_, Pallas>,
                circuit_c2: &mut Circuit<_, Vesta>,
                blinded_point: Option<_>,
                blind: Option<_>| {
    membership_gadget::<_, _, Pasta>(
      &mut OsRng,
      transcript,
      circuit_c1,
      circuit_c2,
      &tree,
      blinded_point,
      blind,
    );
  };

  let mut statements = vec![];
  let mut proofs = vec![];

  let proving = std::time::Instant::now();
  let runs = 10;
  dbg!(runs);
  for _ in 0 .. runs {
    let blind_c1 =
      new_blind::<_, Pallas, Vesta>(&mut OsRng, DLogTable::<Pallas>::new(pallas_h).trits(), 0).0;
    let point = leaves[usize::try_from(OsRng.next_u64() % (1 << 30)).unwrap() % leaves.len()];
    assert!(permissible_c1.point(point));
    let blinded_point = point - (pallas_generators.h().point() * blind_c1);

    let mut prove_transcript = transcript.clone();
    let mut circuit_c1 = Circuit::new(pallas_generators.per_proof(), true);
    let mut circuit_c2 = Circuit::new(vesta_generators.per_proof(), true);
    gadget(&mut prove_transcript, &mut circuit_c1, &mut circuit_c2, Some(blinded_point), Some(blind_c1));

    let (pallas_commitments, _, pallas_vector_commitments, pallas_proof, pallas_proofs) = circuit_c1
      .prove_with_vector_commitments(
        &mut OsRng,
        &mut prove_transcript,
      );
    let (vesta_commitments, _, vesta_vector_commitments, vesta_proof, vesta_proofs) = circuit_c2
      .prove_with_vector_commitments(
        &mut OsRng,
        &mut prove_transcript,
      );

    statements.push(blinded_point);
    proofs.push((
      (pallas_commitments, pallas_vector_commitments, pallas_proof, pallas_proofs),
      (vesta_commitments, vesta_vector_commitments, vesta_proof, vesta_proofs),
    ));
  }
  dbg!(std::time::Instant::now() - proving);

  let initial_circuit_time = std::time::Instant::now();
  let mut circuit_c1 = Circuit::new(pallas_generators.per_proof(), false);
  let mut circuit_c2 = Circuit::new(vesta_generators.per_proof(), false);
  let mut verify_transcript = transcript;
  gadget(&mut verify_transcript, &mut circuit_c1, &mut circuit_c2, None, None);
  let circuit_c1 = circuit_c1.verification_statement_with_vector_commitments();
  let circuit_c2 = circuit_c2.verification_statement_with_vector_commitments();
  dbg!(std::time::Instant::now() - initial_circuit_time);

  let verification = std::time::Instant::now();
  let mut verifier_c1 = BatchVerifier::new((runs * (depth * 3)).try_into().unwrap());
  let mut verifier_c2 = BatchVerifier::new((runs * (depth * 3)).try_into().unwrap());
  for i in 0 .. runs {
    let blinded_point = statements[usize::try_from(i).unwrap()];
    let (
      (pallas_commitments, pallas_vector_commitments, pallas_proof, pallas_proofs),
      (vesta_commitments, vesta_vector_commitments, vesta_proof, vesta_proofs),
    ) = proofs[usize::try_from(i).unwrap()].clone();

    // We need to arrange the points as post-vars
    let mut c1_additional = vec![];
    for (i, commitment) in vesta_vector_commitments.iter().enumerate() {
      if (i % 2) != 1 {
        continue;
      }
      let coords = Pasta::c2_coords(*commitment);
      c1_additional.push(coords.0);
      c1_additional.push(coords.1);
    }
    let blinded_point_coords = Pasta::c1_coords(blinded_point);
    let mut c2_additional = vec![blinded_point_coords.0, blinded_point_coords.1];
    for (i, commitment) in pallas_vector_commitments.iter().enumerate() {
      if (i % 2) != 1 {
        continue;
      }
      let coords = Pasta::c1_coords(*commitment);
      c2_additional.push(coords.0);
      c2_additional.push(coords.1);
    }

    // The caller must check the tree root aligns
    if (tree.depth() % 2) == 1 {
      assert_eq!(Hash::Odd(*vesta_vector_commitments.last().unwrap()), tree.root());
      c1_additional.pop();
      c1_additional.pop();
    } else {
      assert_eq!(Hash::Even(*pallas_vector_commitments.last().unwrap()), tree.root());
      c2_additional.pop();
      c2_additional.pop();
    }

    let mut verify_transcript = verify_transcript.clone();

    circuit_c1.verify(
      &mut OsRng,
      &mut verifier_c1,
      &mut verify_transcript,
      pallas_commitments,
      pallas_vector_commitments,
      &c1_additional,
      pallas_proof,
      pallas_proofs,
    );
    circuit_c2.verify(
      &mut OsRng,
      &mut verifier_c2,
      &mut verify_transcript,
      vesta_commitments,
      vesta_vector_commitments,
      &c2_additional,
      vesta_proof,
      vesta_proofs,
    );
  }
  dbg!(std::time::Instant::now() - verification);

  let batch_verification = std::time::Instant::now();
  assert!(verifier_c1.verify_vartime());
  assert!(verifier_c2.verify_vartime());
  dbg!(std::time::Instant::now() - batch_verification);
}
