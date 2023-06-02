use rand_core::OsRng;

use transcript::{Transcript, RecommendedTranscript};
use ciphersuite::{
  group::{ff::Field, Group},
  Ciphersuite, Ristretto,
};

use crate::{
  arithmetic_circuit::{Constraint, Circuit},
  tests::generators,
};

#[test]
fn test_vector_commitment() {
  let (g, h, g_bold1, g_bold2, h_bold1, h_bold2) = generators(8);
  let (additional_g_1, additional_g_2, additional_hs_1, additional_hs_2, _, _) =
    generators::<Ristretto>(8);
  let additional_gs = (additional_g_1, additional_g_2);
  let additional_hs = (additional_hs_1.0.clone(), additional_hs_2.0.clone());

  let x_bind = <Ristretto as Ciphersuite>::G::random(&mut OsRng);
  let y_bind = <Ristretto as Ciphersuite>::G::random(&mut OsRng);

  let z_bind = <Ristretto as Ciphersuite>::G::random(&mut OsRng);
  let a_bind = <Ristretto as Ciphersuite>::G::random(&mut OsRng);

  fn gadget(
    circuit: &mut Circuit<Ristretto>,
    binds_x_y: (<Ristretto as Ciphersuite>::G, <Ristretto as Ciphersuite>::G),
    x_y: Option<(<Ristretto as Ciphersuite>::F, <Ristretto as Ciphersuite>::F)>,
    binds_z_a: (<Ristretto as Ciphersuite>::G, <Ristretto as Ciphersuite>::G),
    z_a: Option<(<Ristretto as Ciphersuite>::F, <Ristretto as Ciphersuite>::F)>,
  ) {
    let x_var = circuit.add_secret_input(x_y.as_ref().map(|xy| xy.0));
    let y_var = circuit.add_secret_input(x_y.as_ref().map(|xy| xy.1));
    let z_var = circuit.add_secret_input(z_a.as_ref().map(|za| za.0));
    let a_var = circuit.add_secret_input(z_a.as_ref().map(|za| za.1));

    let ((product_l, product_r, _), _) = circuit.product(x_var, y_var);
    let vc = circuit.allocate_vector_commitment();
    circuit.bind(vc, product_l, Some(binds_x_y.0));
    circuit.bind(vc, product_r, Some(binds_x_y.1));

    let ((product_l, _, product_o), _) = circuit.product(z_var, a_var);
    let vc = circuit.allocate_vector_commitment();
    circuit.bind(vc, product_l, Some(binds_z_a.0));
    circuit.bind(vc, product_o, Some(binds_z_a.1));

    circuit.constrain(Constraint::new("empty"));
  }

  let x = <Ristretto as Ciphersuite>::F::random(&mut OsRng);
  let y = <Ristretto as Ciphersuite>::F::random(&mut OsRng);
  let z = <Ristretto as Ciphersuite>::F::random(&mut OsRng);
  let a = <Ristretto as Ciphersuite>::F::random(&mut OsRng);

  let mut transcript = RecommendedTranscript::new(b"Vector Commitment Test");

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
  gadget(&mut circuit, (x_bind, y_bind), Some((x, y)), (z_bind, a_bind), Some((z, a)));
  let (blinds, commitments, proof, proofs) = circuit.prove_with_vector_commitments(
    &mut OsRng,
    &mut transcript.clone(),
    additional_gs,
    additional_hs.clone(),
  );
  assert_eq!(blinds.len(), 2);
  assert_eq!(commitments.len(), 2);
  assert_eq!(proofs.len(), 3);
  assert_eq!(commitments[0], (x_bind * x) + (y_bind * y) + (h * blinds[0]));
  assert_eq!(commitments[1], (z_bind * z) + (a_bind * (z * a)) + (h * blinds[1]));

  let mut circuit =
    Circuit::new(g, h, g_bold1, g_bold2, h_bold1, h_bold2, false, Some(commitments));
  gadget(&mut circuit, (x_bind, y_bind), None, (z_bind, a_bind), None);
  circuit.verify_with_vector_commitments(
    &mut transcript,
    additional_gs,
    additional_hs,
    proof,
    proofs,
  );
}
