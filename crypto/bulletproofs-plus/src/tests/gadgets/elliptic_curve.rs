use rand_core::OsRng;

use subtle::Choice;

use transcript::{Transcript, RecommendedTranscript};
use pasta_curves::arithmetic::CurveAffine;
use ciphersuite::{
  group::{
    ff::{Field, PrimeField, PrimeFieldBits},
    Group,
    prime::PrimeCurveAffine,
  },
  Ciphersuite, Pallas, Vesta,
};

use crate::{
  arithmetic_circuit::{Constraint, Circuit},
  gadgets::elliptic_curve::EmbeddedCurveAddition,
  tests::generators,
};

#[test]
fn test_elliptic_curve_gadget() {
  type PallasAffine = pasta_curves::pallas::Affine;

  let (g, h, g_bold1, g_bold2, h_bold1, h_bold2) = generators(64 * 256);

  // Pasta generators are x: -1, y: 2
  let generator = (-<Vesta as Ciphersuite>::F::ONE, <Vesta as Ciphersuite>::F::ONE.double());
  let gen_coords = PallasAffine::generator().coordinates().unwrap();
  assert_eq!((generator.0, generator.1), (*gen_coords.x(), *gen_coords.y()));

  let alt_generator = <Pallas as Ciphersuite>::G::random(&mut OsRng);

  let p1 = <Pallas as Ciphersuite>::G::random(&mut OsRng);
  let p2 = <Pallas as Ciphersuite>::G::random(&mut OsRng);
  let p3 = p1 + p2;

  let p1 = PallasAffine::from(p1).coordinates().unwrap();
  let p1 = (*p1.x(), *p1.y());

  let p2 = PallasAffine::from(p2).coordinates().unwrap();
  let p2 = (*p2.x(), *p2.y());

  let p3 = PallasAffine::from(p3).coordinates().unwrap();
  let p3 = (*p3.x(), *p3.y());

  let mut transcript = RecommendedTranscript::new(b"Point Addition Circuit Test");

  let gadget = |circuit: &mut Circuit<Vesta>| {
    let prover = circuit.prover();

    let p1_x = circuit.add_secret_input(Some(p1.0).filter(|_| prover));
    let p1_y = circuit.add_secret_input(Some(p1.1).filter(|_| prover));

    let p2_x = circuit.add_secret_input(Some(p2.0).filter(|_| prover));
    let p2_y = circuit.add_secret_input(Some(p2.1).filter(|_| prover));

    <Vesta as EmbeddedCurveAddition>::constrain_on_curve(circuit, p1_x, p1_y);
    <Vesta as EmbeddedCurveAddition>::constrain_on_curve(circuit, p2_x, p2_y);

    let (res_x, res_y) =
      <Vesta as EmbeddedCurveAddition>::incomplete_add(circuit, p1_x, p1_y, p2_x, p2_y);

    let p3_x = circuit.add_constant(p3.0);
    let p3_y = circuit.add_constant(p3.1);
    circuit.constrain_equality(
      circuit.variable_to_product(res_x).unwrap(),
      circuit.variable_to_product(p3_x).unwrap(),
    );
    circuit.constrain_equality(
      circuit.variable_to_product(res_y).unwrap(),
      circuit.variable_to_product(p3_y).unwrap(),
    );
  };

  /*
  // Pick a blind within the capacity
  let mut blind = <Pallas as Ciphersuite>::F::random(&mut OsRng);
  while *blind.to_le_bits().iter().last().unwrap() {
    blind = <Pallas as Ciphersuite>::F::random(&mut OsRng);
  }
  let mut blind_bits = vec![];
  let mut alt_generators = vec![alt_generator];
  for b in blind.to_le_bits().iter().take(<Pallas as Ciphersuite>::F::CAPACITY.try_into().unwrap())
  {
    blind_bits.push(Choice::from(u8::from(*b)));
    alt_generators.push(alt_generators.last().unwrap().double());
  }
  alt_generators.pop();
  let alt_generators_x = alt_generators
    .iter()
    .map(|alt| *PallasAffine::from(*alt).coordinates().unwrap().x())
    .collect::<Vec<_>>();
  let alt_generators_y = alt_generators
    .iter()
    .map(|alt| *PallasAffine::from(*alt).coordinates().unwrap().y())
    .collect::<Vec<_>>();

  let mut p1p2 = (p1 + p2).double();
  p1p2 += alt_generator * blind;
  let p1p2 = PallasAffine::from(p1p2).coordinates().unwrap();
  let (p1p2_x, p1p2_y) = (*p1p2.x(), *p1p2.y());

  let gadget = |circuit: &mut Circuit<Vesta>| {
    <Vesta as EmbeddedCurveAddition>::constrain_on_curve(circuit, p1_x, p1_y);
    <Vesta as EmbeddedCurveAddition>::constrain_on_curve(circuit, p2_x, p2_y);

    let (res_x, res_y) = <Vesta as EmbeddedCurveAddition>::add(circuit, p1_x, p1_y, p2_x, p2_y);

    let (res_x, res_y) = <Vesta as EmbeddedCurveAddition>::double(circuit, res_x, res_y);

    let prover_bits = blind_bits.clone().drain(..).map(Some).collect::<Vec<_>>();
    let verifier_bits = vec![None; <Pallas as Ciphersuite>::F::CAPACITY.try_into().unwrap()];
    let blind_bits = if circuit.prover() { &prover_bits } else { &verifier_bits };

    let (res_x, res_y) = <Vesta as EmbeddedCurveAddition>::scalar_mul_generator(
      circuit,
      res_x,
      res_y,
      &alt_generators_x,
      &alt_generators_y,
      blind_bits,
    );

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
  */

  let mut circuit =
    Circuit::new(g, h, g_bold1.clone(), g_bold2.clone(), h_bold1.clone(), h_bold2.clone(), true);
  gadget(&mut circuit);
  let proof = circuit.prove(&mut OsRng, &mut transcript.clone());

  let mut circuit = Circuit::new(g, h, g_bold1, g_bold2, h_bold1, h_bold2, false);
  gadget(&mut circuit);
  circuit.verify(&mut transcript, proof);
}
