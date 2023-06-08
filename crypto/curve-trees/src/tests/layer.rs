use rand_core::{RngCore, OsRng};

use transcript::{Transcript, RecommendedTranscript};

use multiexp::BatchVerifier;
use ciphersuite::{
  group::{ff::Field, Group},
  Ciphersuite, Pallas, Vesta,
};

use ecip::Ecip;
use bulletproofs_plus::{
  arithmetic_circuit::Circuit, gadgets::elliptic_curve::DLogTable, tests::generators,
};

use crate::{
  CurveCycle, pedersen_hash::pedersen_hash_vartime, permissible::Permissible, new_blind,
  layer_gadget, tests::Pasta,
};

#[test]
fn test_layer_gadget() {
  let (g, h, g_bold1, g_bold2, h_bold1, h_bold2) = generators::<Vesta>(1024 * 8);
  let (additional_g_0, additional_g_1, additional_hs_0, additional_hs_1, _, _) =
    generators::<Vesta>(1024 * 8);
  let additional_gs = (additional_g_0, additional_g_1);
  let additional_hs = (additional_hs_0.0.clone(), additional_hs_1.0.clone());

  let permissible = Permissible::<<Pasta as CurveCycle>::C1> {
    h: <<Pasta as CurveCycle>::C1 as Ciphersuite>::G::random(&mut OsRng),
    alpha: <<Pasta as CurveCycle>::C1 as Ecip>::FieldElement::random(&mut OsRng),
    beta: <<Pasta as CurveCycle>::C1 as Ecip>::FieldElement::random(&mut OsRng),
  };

  let H = <Pallas as Ciphersuite>::G::random(&mut OsRng);

  let mut pedersen_generators = vec![];
  for _ in 0 .. 4 {
    pedersen_generators.push(<Vesta as Ciphersuite>::G::random(&mut OsRng));
  }

  let mut elems = vec![];
  let mut raw_elems = vec![];
  let mut formatted_elems = vec![];
  for _ in 0 .. 4 {
    elems.push(permissible.make_permissible(<Pallas as Ciphersuite>::G::random(&mut OsRng)).1);
    let x = Pasta::c1_coords(*elems.last().unwrap()).0;
    raw_elems.push(x);
    formatted_elems.push(Some(x));
  }

  let (blind_c1, blind_c2) = new_blind::<_, Pallas, Vesta>(&mut OsRng, 0);
  let point = elems[usize::try_from(OsRng.next_u64() % 4).unwrap()];
  // Uses - so the blind is added back
  let blinded_point = point - (H * blind_c1);

  let gadget = |circuit: &mut Circuit<Vesta>| {
    layer_gadget::<_, Pasta>(
      &mut OsRng,
      circuit,
      &permissible,
      &DLogTable::new(H),
      &pedersen_generators,
      blinded_point,
      Some(blind_c2).filter(|_| circuit.prover()),
      0,
      formatted_elems.iter().cloned().map(|x| x.filter(|_| circuit.prover())).collect(),
      false,
    )
  };

  let mut transcript = RecommendedTranscript::new(b"Layer Gadget Test");

  let mut circuit = Circuit::new(
    g,
    h,
    g_bold1.clone(),
    g_bold2.clone(),
    h_bold1.clone(),
    h_bold2.clone(),
    true,
    None,
  );
  gadget(&mut circuit);
  let (blinds, commitments, proof, proofs) = circuit.prove_with_vector_commitments(
    &mut OsRng,
    &mut transcript.clone(),
    additional_gs,
    additional_hs.clone(),
  );

  assert_eq!(commitments.len(), 2);
  assert_eq!(
    *commitments.last().unwrap() - (h * blinds.last().unwrap()),
    pedersen_hash_vartime::<Vesta>(&raw_elems, &pedersen_generators)
  );

  let mut circuit =
    Circuit::new(g, h, g_bold1, g_bold2, h_bold1, h_bold2, false, Some(commitments));
  gadget(&mut circuit);
  let mut verifier = BatchVerifier::new(5);
  circuit.verify_with_vector_commitments(
    &mut OsRng,
    &mut verifier,
    &mut transcript,
    additional_gs,
    additional_hs,
    proof,
    proofs,
  );
  assert!(verifier.verify_vartime());
}
