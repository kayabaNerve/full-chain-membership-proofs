use rand_core::OsRng;

use transcript::{Transcript, RecommendedTranscript};

use multiexp::BatchVerifier;
use ciphersuite::{
  group::{ff::Field, Group},
  Ciphersuite, Ristretto,
};

use crate::{
  VectorCommitmentGenerators,
  arithmetic_circuit::{Constraint, Circuit},
  tests::generators as generators_fn,
};

#[test]
fn test_vector_commitment() {
  let mut generators = generators_fn(8);

  let x_bind = <Ristretto as Ciphersuite>::G::random(&mut OsRng);
  let y_bind = <Ristretto as Ciphersuite>::G::random(&mut OsRng);

  let z_bind = <Ristretto as Ciphersuite>::G::random(&mut OsRng);
  let a_bind = <Ristretto as Ciphersuite>::G::random(&mut OsRng);

  let x = <Ristretto as Ciphersuite>::F::random(&mut OsRng);
  let y = <Ristretto as Ciphersuite>::F::random(&mut OsRng);
  let z = <Ristretto as Ciphersuite>::F::random(&mut OsRng);
  let a = <Ristretto as Ciphersuite>::F::random(&mut OsRng);

  let mut expected_commitment_0 = None;
  let mut expected_commitment_1 = None;

  let gens_0 = VectorCommitmentGenerators::new(&[x_bind, y_bind]);
  generators.whitelist_vector_commitments(b"Vector Commitment 0", &gens_0);
  let gens_1 = VectorCommitmentGenerators::new(&[z_bind, a_bind]);
  generators.whitelist_vector_commitments(b"Vector Commitment 1", &gens_1);

  let mut gadget =
    |circuit: &mut Circuit<RecommendedTranscript, Ristretto>,
     x_y: Option<(<Ristretto as Ciphersuite>::F, <Ristretto as Ciphersuite>::F)>,
     z_a: Option<(<Ristretto as Ciphersuite>::F, <Ristretto as Ciphersuite>::F)>| {
      let x_var = circuit.add_secret_input(x_y.as_ref().map(|xy| xy.0));
      let y_var = circuit.add_secret_input(x_y.as_ref().map(|xy| xy.1));
      let z_var = circuit.add_secret_input(z_a.as_ref().map(|za| za.0));
      let a_var = circuit.add_secret_input(z_a.as_ref().map(|za| za.1));

      let ((product_l, product_r, _), _) = circuit.product(x_var, y_var);
      let vc = circuit.allocate_vector_commitment();
      circuit.bind(vc, vec![product_l, product_r], Some(&gens_0));
      // TODO: Panic if a circuit doesn't finalize VCs
      {
        let blind = <Ristretto as Ciphersuite>::F::random(&mut OsRng);
        expected_commitment_0 =
          expected_commitment_0.or(Some((x_bind * x) + (y_bind * y) + (generators.h() * blind)));
        assert_eq!(
          circuit.finalize_commitment(vc, Some(blind).filter(|_| circuit.prover())),
          expected_commitment_0.unwrap()
        );
      }

      let ((product_l, _, product_o), _) = circuit.product(z_var, a_var);
      let vc = circuit.allocate_vector_commitment();
      circuit.bind(vc, vec![product_l, product_o], Some(&gens_1));
      {
        let blind = <Ristretto as Ciphersuite>::F::random(&mut OsRng);
        expected_commitment_1 = expected_commitment_1
          .or(Some((z_bind * z) + (a_bind * (z * a)) + (generators.h() * blind)));
        assert_eq!(
          circuit.finalize_commitment(vc, Some(blind).filter(|_| circuit.prover()),),
          expected_commitment_1.unwrap()
        );
      }

      circuit.constrain(Constraint::new("empty"));
    };

  let mut transcript = RecommendedTranscript::new(b"Vector Commitment Test");

  let mut circuit = Circuit::new(generators.clone(), true, None);
  gadget(&mut circuit, Some((x, y)), Some((z, a)));
  let (blinds, commitments, proof, proofs) =
    circuit.prove_with_vector_commitments(&mut OsRng, &mut transcript.clone());
  assert_eq!(blinds.len(), 2);
  assert_eq!(commitments.len(), 2);
  assert_eq!(proofs.len(), 3);

  let mut circuit = Circuit::new(generators.clone(), false, Some(commitments.clone()));
  gadget(&mut circuit, None, None);
  let mut verifier = BatchVerifier::new(5);
  circuit.verify_with_vector_commitments(&mut OsRng, &mut verifier, &mut transcript, proof, proofs);
  assert!(verifier.verify_vartime());

  assert_eq!(commitments[0], expected_commitment_0.unwrap());
  assert_eq!(commitments[1], expected_commitment_1.unwrap());
}
