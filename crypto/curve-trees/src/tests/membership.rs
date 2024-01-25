use rand_core::{RngCore, OsRng};

use transcript::{Transcript, RecommendedTranscript};

use multiexp::BatchVerifier;
use ciphersuite::{
  group::{ff::Field, Group, GroupEncoding},
  Ciphersuite, Pallas, Vesta,
};

use ecip::Ecip;
use bulletproofs_plus::{
  GeneratorsList, arithmetic_circuit::Circuit, gadgets::elliptic_curve::DLogTable,
  tests::generators as generators_fn,
};

use crate::{
  CurveCycle,
  permissible::Permissible,
  tree::{Hash, Tree},
  tests::Pasta,
  new_blind, membership_gadget,
};

#[test]
fn test_membership() {
  let leaf_randomness = <<Pasta as CurveCycle>::C1 as Ciphersuite>::G::random(&mut OsRng);

  let mut verifier_c1 = BatchVerifier::new(3 + (3 * 4));
  let mut verifier_c2 = BatchVerifier::new(3 + (3 * 4));

  // Test with various widths
  for width in 2 ..= 4usize {
    let mut pallas_generators = generators_fn::<Pallas>(512 * 4);
    let mut vesta_generators = generators_fn::<Vesta>(512 * 4);

    let pallas_h = pallas_generators.h().point();
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

    let mut even_generators = vec![];
    let mut odd_generators = vec![];
    for i in 0 .. width {
      even_generators
        .push(pallas_generators.per_proof().generator(GeneratorsList::GBold1, i).point());
      odd_generators
        .push(vesta_generators.per_proof().generator(GeneratorsList::GBold1, i).point());
    }

    let max = u64::try_from(width).unwrap().pow(4);
    let mut tree = Tree::<RecommendedTranscript, Pasta>::new(
      odd_generators,
      even_generators,
      permissible_c1,
      permissible_c2,
      leaf_randomness,
      width,
      max,
    );

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
    let blinded_point = point - (pallas_generators.h().point() * blind_c1);

    let gadget = |transcript: &mut RecommendedTranscript,
                  circuit_c1: &mut Circuit<_, Pallas>,
                  circuit_c2: &mut Circuit<_, Vesta>| {
      membership_gadget::<_, _, Pasta>(
        &mut OsRng,
        transcript,
        circuit_c1,
        circuit_c2,
        &tree,
        Some(blinded_point).filter(|_| circuit_c1.prover()),
        Some(blind_c1).filter(|_| circuit_c1.prover()),
      );
    };

    let mut transcript = RecommendedTranscript::new(b"Membership Gadget Test");

    // Prove
    let mut prove_transcript = transcript.clone();
    let mut circuit_c1 = Circuit::new(pallas_generators.per_proof(), true);
    let mut circuit_c2 = Circuit::new(vesta_generators.per_proof(), true);
    gadget(&mut prove_transcript, &mut circuit_c1, &mut circuit_c2);

    // Opportunity to transcript anything else relevant
    prove_transcript.append_message(b"blinded_point", blinded_point.to_bytes());
    prove_transcript.append_message(
      b"tree_root",
      match tree.root() {
        Hash::Even(even) => even.to_bytes(),
        Hash::Odd(odd) => odd.to_bytes(),
      },
    );

    let (pallas_commitments, _, pallas_vector_commitments, pallas_proof) =
      circuit_c1.prove(&mut OsRng, &mut prove_transcript);
    let (vesta_commitments, _, vesta_vector_commitments, vesta_proof) =
      circuit_c2.prove(&mut OsRng, &mut prove_transcript);

    // Verify
    let mut circuit_c1 = Circuit::new(pallas_generators.per_proof(), false);
    let mut circuit_c2 = Circuit::new(vesta_generators.per_proof(), false);
    gadget(&mut transcript, &mut circuit_c1, &mut circuit_c2);

    transcript.append_message(b"blinded_point", blinded_point.to_bytes());
    transcript.append_message(
      b"tree_root",
      match tree.root() {
        Hash::Even(even) => even.to_bytes(),
        Hash::Odd(odd) => odd.to_bytes(),
      },
    );

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

    circuit_c1.verification_statement().verify(
      &mut OsRng,
      &mut verifier_c1,
      &mut transcript,
      pallas_commitments,
      pallas_vector_commitments,
      c1_additional,
      pallas_proof,
    );
    circuit_c2.verification_statement().verify(
      &mut OsRng,
      &mut verifier_c2,
      &mut transcript,
      vesta_commitments,
      vesta_vector_commitments,
      c2_additional,
      vesta_proof,
    );
  }

  assert!(verifier_c1.verify_vartime());
  assert!(verifier_c2.verify_vartime());
}
