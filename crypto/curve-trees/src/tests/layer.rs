use rand_core::{RngCore, OsRng};

use transcript::{Transcript, RecommendedTranscript};
use ciphersuite::{group::Group, Ciphersuite, Pallas, Vesta};

use bulletproofs_plus::{
  arithmetic_circuit::Circuit, gadgets::elliptic_curve::DLogTable, tests::generators,
};

#[rustfmt::skip]
use crate::{CurveCycle, pedersen_hash::pedersen_hash_vartime, new_blind, layer_gadget, tests::Pasta};

#[test]
fn test_layer_gadget() {
  let (g, h, g_bold1, g_bold2, h_bold1, h_bold2) = generators::<Vesta>(1024 * 8);
  let (additional_g_0, additional_g_1, additional_hs_0, additional_hs_1, _, _) =
    generators::<Vesta>(1024 * 8);
  let additional_gs = (additional_g_0, additional_g_1);
  let additional_hs = (additional_hs_0.0.clone(), additional_hs_1.0.clone());

  let H = <Pallas as Ciphersuite>::G::random(&mut OsRng);

  let mut pedersen_generators = vec![];
  for _ in 0 .. 8 {
    pedersen_generators.push(<Vesta as Ciphersuite>::G::random(&mut OsRng));
  }

  let mut elems = vec![];
  let mut raw_elems = vec![];
  let mut formatted_elems = vec![];
  for _ in 0 .. 4 {
    elems.push(<Pallas as Ciphersuite>::G::random(&mut OsRng));
    let (x, y) = Pasta::c1_coords(*elems.last().unwrap());
    raw_elems.push(x);
    raw_elems.push(y);
    formatted_elems.push((Some(x), Some(y)));
  }

  let (blind_c1, blind_c2) = new_blind::<_, Pallas, Vesta>(&mut OsRng);
  let point = elems[usize::try_from(OsRng.next_u64() % 4).unwrap()];
  // Uses - so the blind is added back
  let blinded_point = point - (H * blind_c1);

  let gadget = |circuit: &mut Circuit<Vesta>| {
    layer_gadget::<_, Pasta>(
      &mut OsRng,
      circuit,
      &DLogTable::new(H),
      &pedersen_generators,
      blinded_point,
      Some(blind_c2).filter(|_| circuit.prover()),
      formatted_elems
        .iter()
        .cloned()
        .map(|(x, y)| (x.filter(|_| circuit.prover()), y.filter(|_| circuit.prover())))
        .collect(),
      false,
    );
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
  circuit.verify_with_vector_commitments(
    &mut transcript,
    additional_gs,
    additional_hs,
    proof,
    proofs,
  );
}
