use rand_core::{RngCore, OsRng};

use transcript::{Transcript, RecommendedTranscript};

use multiexp::BatchVerifier;
use ciphersuite::{
  group::{ff::Field, Group},
  Ciphersuite, Pallas, Vesta,
};

use ecip::Ecip;
use bulletproofs_plus::{
  VectorCommitmentGenerators, arithmetic_circuit::Circuit, gadgets::elliptic_curve::DLogTable,
  tests::generators as generators_fn,
};

use crate::{CurveCycle, permissible::Permissible, new_blind, layer_gadget, tests::Pasta};

#[test]
fn test_layer_gadget() {
  let mut generators = generators_fn::<Vesta>(2048);

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
  let pedersen_generators = VectorCommitmentGenerators::new(&pedersen_generators);
  generators.whitelist_vector_commitments(b"Pedersen Hash Generators", &pedersen_generators);

  let mut elems = vec![];
  let mut raw_elems = vec![];
  let mut formatted_elems = vec![];
  for _ in 0 .. 4 {
    elems.push(permissible.make_permissible(<Pallas as Ciphersuite>::G::random(&mut OsRng)).1);
    let x = Pasta::c1_coords(*elems.last().unwrap()).0;
    raw_elems.push(x);
    formatted_elems.push(Some(x));
  }

  let H_table = DLogTable::new(H);
  let blind_c1 = new_blind::<_, Pallas, Vesta>(&mut OsRng, H_table.trits(), 0).0;
  let point = elems[usize::try_from(OsRng.next_u64() % 4).unwrap()];
  // Uses - so the blind is added back
  let blinded_point = point - (H * blind_c1);

  let gadget = |circuit: &mut Circuit<_, Vesta>| {
    layer_gadget::<_, _, Pasta>(
      &mut OsRng,
      circuit,
      &permissible,
      &H_table,
      &pedersen_generators,
      blinded_point,
      Some(blind_c1).filter(|_| circuit.prover()),
      0,
      formatted_elems.iter().cloned().map(|x| x.filter(|_| circuit.prover())).collect(),
      false,
    )
  };

  let mut transcript = RecommendedTranscript::new(b"Layer Gadget Test");

  let mut circuit = Circuit::new(generators.per_proof(), true, None);
  gadget(&mut circuit);
  let (blinds, commitments, proof, proofs) =
    circuit.prove_with_vector_commitments(&mut OsRng, &mut transcript.clone());

  assert_eq!(commitments.len(), 2);
  assert_eq!(
    *commitments.last().unwrap() - (generators.h().point() * blinds.last().unwrap()),
    pedersen_generators.commit_vartime(&raw_elems),
  );

  let mut circuit = Circuit::new(generators.per_proof(), false, Some(commitments));
  gadget(&mut circuit);
  let mut verifier = BatchVerifier::new(5);
  circuit.verify_with_vector_commitments(&mut OsRng, &mut verifier, &mut transcript, proof, proofs);
  assert!(verifier.verify_vartime());
}
