use rand_core::{RngCore, OsRng};

use transcript::{Transcript, RecommendedTranscript};
use ciphersuite::{group::Group, Ciphersuite, Pallas, Vesta};

use bulletproofs_plus::{arithmetic_circuit::Circuit, tests::generators};

use crate::{
  CurveCycle,
  tree::Tree,
  tests::Pasta,
  new_blind, membership_gadget,
};

#[test]
fn test_membership() {
  let (pallas_g, pallas_h, pallas_g_bold1, pallas_g_bold2, pallas_h_bold1, pallas_h_bold2) =
    generators::<Pallas>(1024 * 32);
  let (
    pallas_additional_g_0,
    pallas_additional_g_1,
    pallas_additional_hs_0,
    pallas_additional_hs_1,
    _,
    _,
  ) = generators::<Pallas>(1024 * 32);
  let pallas_additional_gs = (pallas_additional_g_0, pallas_additional_g_1);
  let pallas_additional_hs = (pallas_additional_hs_0.0.clone(), pallas_additional_hs_1.0.clone());

  let (vesta_g, vesta_h, vesta_g_bold1, vesta_g_bold2, vesta_h_bold1, vesta_h_bold2) =
    generators::<Vesta>(1024 * 32);
  let (
    vesta_additional_g_0,
    vesta_additional_g_1,
    vesta_additional_hs_0,
    vesta_additional_hs_1,
    _,
    _,
  ) = generators::<Vesta>(1024 * 32);
  let vesta_additional_gs = (vesta_additional_g_0, vesta_additional_g_1);
  let vesta_additional_hs = (vesta_additional_hs_0.0.clone(), vesta_additional_hs_1.0.clone());

  // Test with various widths
  for width in 2 ..= 4usize {
    let max = u64::try_from(width).unwrap().pow(4);
    let mut tree = Tree::<Pasta>::new(width, max);

    // Create a full tree
    let mut leaves = vec![];
    for _ in 0 .. max {
      leaves.push(<<Pasta as CurveCycle>::C1 as Ciphersuite>::G::random(&mut OsRng));
    }
    tree.add_leaves(&leaves);

    let (blind_c1, blind_c2) = new_blind::<_, Pallas, Vesta>(&mut OsRng);
    let point = leaves[usize::try_from(OsRng.next_u64() % (1 << 30)).unwrap() % leaves.len()];
    let blinded_point = point - (pallas_h * blind_c1);

    let gadget = |circuit_c1: &mut Circuit<Pallas>, circuit_c2: &mut Circuit<Vesta>| {
      membership_gadget::<_, Pasta>(
        &mut OsRng,
        circuit_c1,
        circuit_c2,
        &tree,
        blinded_point,
        Some((blind_c1, blind_c2)).filter(|_| circuit_c1.prover()),
      );
    };

    let mut transcript = RecommendedTranscript::new(b"Membership Gadget Test");

    let mut circuit_c1 = Circuit::new(
      pallas_g,
      pallas_h,
      pallas_g_bold1.clone(),
      pallas_g_bold2.clone(),
      pallas_h_bold1.clone(),
      pallas_h_bold2.clone(),
      true,
      None,
    );
    let mut circuit_c2 = Circuit::new(
      vesta_g,
      vesta_h,
      vesta_g_bold1.clone(),
      vesta_g_bold2.clone(),
      vesta_h_bold1.clone(),
      vesta_h_bold2.clone(),
      true,
      None,
    );
    gadget(&mut circuit_c1, &mut circuit_c2);

    let mut prove_transcript = transcript.clone();
    let (_, pallas_commitments, pallas_proof, pallas_proofs) = circuit_c1
      .prove_with_vector_commitments(
        &mut OsRng,
        &mut prove_transcript,
        pallas_additional_gs,
        pallas_additional_hs.clone(),
      );
    let (_, vesta_commitments, vesta_proof, vesta_proofs) = circuit_c2
      .prove_with_vector_commitments(
        &mut OsRng,
        &mut prove_transcript,
        vesta_additional_gs,
        vesta_additional_hs.clone(),
      );

    let mut circuit_c1 = Circuit::new(
      pallas_g,
      pallas_h,
      pallas_g_bold1.clone(),
      pallas_g_bold2.clone(),
      pallas_h_bold1.clone(),
      pallas_h_bold2.clone(),
      false,
      Some(pallas_commitments),
    );
    let mut circuit_c2 = Circuit::new(
      vesta_g,
      vesta_h,
      vesta_g_bold1.clone(),
      vesta_g_bold2.clone(),
      vesta_h_bold1.clone(),
      vesta_h_bold2.clone(),
      false,
      Some(vesta_commitments),
    );
    gadget(&mut circuit_c1, &mut circuit_c2);
    circuit_c1.verify_with_vector_commitments(
      &mut transcript,
      pallas_additional_gs,
      pallas_additional_hs.clone(),
      pallas_proof,
      pallas_proofs,
    );
    circuit_c2.verify_with_vector_commitments(
      &mut transcript,
      vesta_additional_gs,
      vesta_additional_hs.clone(),
      vesta_proof,
      vesta_proofs,
    );
  }
}