use rand_core::{RngCore, OsRng};

use transcript::{Transcript, RecommendedTranscript};

use multiexp::BatchVerifier;
use ciphersuite::{
  group::{ff::Field, Group},
  Ciphersuite, Pallas, Vesta,
};

use ecip::Ecip;
use bulletproofs_plus::{
  GeneratorsList, arithmetic_circuit::Circuit, gadgets::elliptic_curve::DLogTable,
  tests::generators as generators_fn,
};

use crate::{
  CurveCycle, permissible::Permissible, pedersen_hash::pedersen_hash_vartime, new_blind,
  layer_gadget, tests::Pasta,
};

#[test]
fn test_layer_gadget() {
  let mut generators = generators_fn::<Vesta>(2048);

  let permissible = Permissible::<<Pasta as CurveCycle>::C1> {
    h: <<Pasta as CurveCycle>::C1 as Ciphersuite>::G::random(&mut OsRng),
    alpha: <<Pasta as CurveCycle>::C1 as Ecip>::FieldElement::random(&mut OsRng),
    beta: <<Pasta as CurveCycle>::C1 as Ecip>::FieldElement::random(&mut OsRng),
  };

  let H = <Pallas as Ciphersuite>::G::random(&mut OsRng);

  let mut elems = vec![];
  let mut raw_elems = vec![];
  let mut formatted_elems = vec![];
  for _ in 0 .. 4 {
    elems.push(permissible.make_permissible(<Pallas as Ciphersuite>::G::random(&mut OsRng)).1);
    let x = Pasta::c1_coords(*elems.last().unwrap()).0;
    raw_elems.push(x);
    formatted_elems.push(Some(x));
  }

  let H_table: &'static DLogTable<Pallas> = Box::leak(Box::new(DLogTable::new(H)));
  let blind_c1 = new_blind::<_, Pallas, Vesta>(&mut OsRng, H_table.trits(), 0).0;
  let point = elems[usize::try_from(OsRng.next_u64() % 4).unwrap()];
  // Uses - so the blind is added back
  let blinded_point = point - (H * blind_c1);

  let mut transcript = RecommendedTranscript::new(b"Layer Gadget Test");

  let gadget = |circuit: &mut Circuit<_, Vesta>| {
    layer_gadget::<_, _, Pasta>(
      &mut OsRng,
      circuit,
      &permissible,
      H_table,
      Some(blinded_point).filter(|_| circuit.prover()),
      Some(blind_c1).filter(|_| circuit.prover()),
      0,
      formatted_elems.iter().cloned().map(|x| x.filter(|_| circuit.prover())).collect(),
      false,
    )
  };

  let (commitments, blinds, vector_commitments, proof) = {
    let mut transcript = transcript.clone();
    let mut circuit = Circuit::new(generators.per_proof(), true);
    gadget(&mut circuit);
    circuit.prove(&mut OsRng, &mut transcript)
  };

  let mut generators_vec = vec![];
  for i in 0 .. raw_elems.len() {
    generators_vec.push(generators.per_proof().generator(GeneratorsList::GBold1, i).point());
  }

  assert!(commitments.is_empty());
  assert_eq!(vector_commitments.len(), 2);
  assert_eq!(
    *vector_commitments.last().unwrap() - (generators.h().point() * blinds.last().unwrap()),
    pedersen_hash_vartime::<Vesta>(&raw_elems, &generators_vec),
  );

  let mut circuit = Circuit::new(generators.per_proof(), false);
  gadget(&mut circuit);
  let mut verifier = BatchVerifier::new(5);
  circuit.verification_statement().verify(
    &mut OsRng,
    &mut verifier,
    &mut transcript,
    commitments,
    vector_commitments,
    vec![Pasta::c1_coords(blinded_point).0, Pasta::c1_coords(blinded_point).1],
    proof,
  );
  assert!(verifier.verify_vartime());
}
