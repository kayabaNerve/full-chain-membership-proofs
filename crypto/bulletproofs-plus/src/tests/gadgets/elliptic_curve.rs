use rand_core::OsRng;

use transcript::{Transcript, RecommendedTranscript};
use pasta_curves::arithmetic::CurveAffine;
use ciphersuite::{
  group::{ff::Field, Group, prime::PrimeCurveAffine},
  Ciphersuite, Pallas, Vesta,
};

use crate::{
  arithmetic_circuit::{Constraint, Circuit},
  gadgets::elliptic_curve::EmbeddedCurveAddition,
  tests::generators,
};

#[test]
fn test_point_addition() {
  type PallasAffine = pasta_curves::pallas::Affine;

  let (g_bold1, g_bold2, h_bold1, h_bold2) = generators(128);

  // Pasta generators are x: -1, y: 2
  let generator = (-<Vesta as Ciphersuite>::F::ONE, <Vesta as Ciphersuite>::F::ONE.double());
  let gen_coords = PallasAffine::generator().coordinates().unwrap();
  assert_eq!((generator.0, generator.1), (*gen_coords.x(), *gen_coords.y()));

  let p1 = <Pallas as Ciphersuite>::G::random(&mut OsRng);
  let p2 = <Pallas as Ciphersuite>::G::random(&mut OsRng);
  let p1p2 = PallasAffine::from(p1 + p2).coordinates().unwrap();
  let (p1p2_x, p1p2_y) = (*p1p2.x(), *p1p2.y());

  let p1 = PallasAffine::from(p1).coordinates().unwrap();
  let p1 = (*p1.x(), *p1.y(), <Vesta as Ciphersuite>::F::ONE);

  let p2 = PallasAffine::from(p2).coordinates().unwrap();
  let p2 = (*p2.x(), *p2.y());

  let mut transcript = RecommendedTranscript::new(b"Point Addition Circuit Test");

  let gadget = |circuit: &mut Circuit<Vesta>| {
    let prover = circuit.prover();

    let p1_x = circuit.add_secret_input(Some(p1.0).filter(|_| prover));
    let p1_y = circuit.add_secret_input(Some(p1.1).filter(|_| prover));

    let p2_x = circuit.add_secret_input(Some(p2.0).filter(|_| prover));
    let p2_y = circuit.add_secret_input(Some(p2.1).filter(|_| prover));

    let (res_x, res_y) = <Vesta as EmbeddedCurveAddition>::add(circuit, p1_x, p1_y, p2_x, p2_y);

    let mut x_constraint = Constraint::new("x");
    x_constraint
      .weight(circuit.variable_to_product(res_x).unwrap(), <Vesta as Ciphersuite>::F::ONE);
    x_constraint.rhs_offset(p1p2_x);
    circuit.constrain(x_constraint);

    let mut y_constraint = Constraint::new("y");
    y_constraint
      .weight(circuit.variable_to_product(res_y).unwrap(), <Vesta as Ciphersuite>::F::ONE);
    y_constraint.rhs_offset(p1p2_y);
    circuit.constrain(y_constraint);
  };

  let mut circuit =
    Circuit::new(g_bold1.clone(), g_bold2.clone(), h_bold1.clone(), h_bold2.clone(), true);
  gadget(&mut circuit);
  let proof = circuit.prove(&mut OsRng, &mut transcript.clone());

  let mut circuit = Circuit::new(g_bold1, g_bold2, h_bold1, h_bold2, false);
  gadget(&mut circuit);
  circuit.verify(&mut transcript, proof);
}
