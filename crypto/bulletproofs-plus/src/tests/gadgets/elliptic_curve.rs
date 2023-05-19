use rand_core::OsRng;

use transcript::{Transcript, RecommendedTranscript};
use pasta_curves::arithmetic::CurveAffine;
use ciphersuite::{
  group::{ff::Field, Group, prime::PrimeCurveAffine},
  Ciphersuite, Vesta,
};

use crate::{
  PointVector,
  arithmetic_circuit::{Constraint, Circuit},
  gadgets::elliptic_curve::EmbeddedCurveAddition,
};

type Generators = (PointVector<Vesta>, PointVector<Vesta>, PointVector<Vesta>, PointVector<Vesta>);

fn generators(n: usize) -> Generators {
  let gens = || {
    let mut res = PointVector::<Vesta>::new(n);
    for i in 0 .. n {
      res[i] = <Vesta as Ciphersuite>::G::random(&mut OsRng);
    }
    res
  };
  (gens(), gens(), gens(), gens())
}

#[test]
fn test_point_addition() {
  type PallasAffine = pasta_curves::pallas::Affine;

  let (g_bold1, g_bold2, h_bold1, h_bold2) = generators(128);

  // Pasta generators are x: -1, y: 2
  let generator = (
    -<Vesta as Ciphersuite>::F::ONE,
    <Vesta as Ciphersuite>::F::ONE.double(),
    <Vesta as Ciphersuite>::F::ONE,
  );
  let gen_coords = PallasAffine::generator().coordinates().unwrap();
  assert_eq!((generator.0, generator.1), (*gen_coords.x(), *gen_coords.y()));
  let z = <Vesta as Ciphersuite>::F::random(&mut OsRng);

  let p1z = <Vesta as Ciphersuite>::F::random(&mut OsRng);
  let p1 = (generator.0 * p1z, generator.1 * p1z, p1z);
  let p2 = generator;

  let p1_point = PallasAffine::generator();
  let p2_point = PallasAffine::from_xy(p2.0, p2.1).unwrap();
  let p1p2 = PallasAffine::from(p1_point + p2_point).coordinates().unwrap();
  let (p1p2_x, p1p2_y) = (*p1p2.x(), *p1p2.y());

  let mut transcript = RecommendedTranscript::new(b"Point Addition Circuit Test");

  let gadget = |circuit: &mut Circuit<Vesta>| {
    let prover = circuit.prover();

    let p1_x = circuit.add_secret_input(Some(p1.0).filter(|_| prover));
    let p1_y = circuit.add_secret_input(Some(p1.1).filter(|_| prover));
    let p1_z = circuit.add_secret_input(Some(p1.2).filter(|_| prover));

    let p2_x = circuit.add_secret_input(Some(p2.0).filter(|_| prover));
    let p2_y = circuit.add_secret_input(Some(p2.1).filter(|_| prover));

    let (res_x, res_y, res_z) =
      <Vesta as EmbeddedCurveAddition>::add(circuit, p1_x, p1_y, p1_z, p2_x, p2_y);

    let (res_x, res_y) = <Vesta as EmbeddedCurveAddition>::normalize(circuit, res_x, res_y, res_z);

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
