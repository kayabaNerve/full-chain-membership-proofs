use rand_core::OsRng;

use transcript::{Transcript, RecommendedTranscript};

use pasta_curves::arithmetic::CurveAffine;
use multiexp::BatchVerifier;
use ciphersuite::{
  group::{
    ff::{Field, PrimeField, PrimeFieldBits},
    Group, Curve,
  },
  Ciphersuite, Pallas, Vesta,
};

use crate::{
  arithmetic_circuit::Circuit,
  gadgets::{
    Bit,
    elliptic_curve::{DLogTable, EmbeddedCurveOperations},
  },
  tests::generators,
};

#[test]
fn test_incomplete_addition() {
  let (g, h, g_bold1, g_bold2, h_bold1, h_bold2) = generators(64 * 256);

  let p1 = <Pallas as Ciphersuite>::G::random(&mut OsRng);
  let p2 = <Pallas as Ciphersuite>::G::random(&mut OsRng);
  let p3 = p1 + p2;

  let p1 = p1.to_affine().coordinates().unwrap();
  let p1 = (*p1.x(), *p1.y());

  let p2_orig = p2;
  let p2 = p2.to_affine().coordinates().unwrap();
  let p2 = (*p2.x(), *p2.y());

  let p3 = p3.to_affine().coordinates().unwrap();
  let p3 = (*p3.x(), *p3.y());

  let mut transcript = RecommendedTranscript::new(b"Point Addition Circuit Test");

  let gadget = |circuit: &mut Circuit<Vesta>| {
    let prover = circuit.prover();

    let p1_x = circuit.add_secret_input(Some(p1.0).filter(|_| prover));
    let p1_y = circuit.add_secret_input(Some(p1.1).filter(|_| prover));

    let p2_x = circuit.add_secret_input(Some(p2.0).filter(|_| prover));
    let p2_y = circuit.add_secret_input(Some(p2.1).filter(|_| prover));

    let p1 = <Vesta as EmbeddedCurveOperations>::constrain_on_curve(circuit, p1_x, p1_y);
    let p2 = <Vesta as EmbeddedCurveOperations>::constrain_on_curve(circuit, p2_x, p2_y);

    let res = <Vesta as EmbeddedCurveOperations>::incomplete_add(circuit, p1, p2);
    circuit.equals_constant(circuit.variable_to_product(res.x()).unwrap(), p3.0);
    circuit.equals_constant(circuit.variable_to_product(res.y()).unwrap(), p3.1);

    let res = <Vesta as EmbeddedCurveOperations>::incomplete_add_constant(circuit, p1, p2_orig);
    circuit.equals_constant(circuit.variable_to_product(res.x()).unwrap(), p3.0);
    circuit.equals_constant(circuit.variable_to_product(res.y()).unwrap(), p3.1);
  };

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
  let proof = circuit.prove(&mut OsRng, &mut transcript.clone());

  let mut circuit = Circuit::new(g, h, g_bold1, g_bold2, h_bold1, h_bold2, false, Some(vec![]));
  gadget(&mut circuit);
  let mut verifier = BatchVerifier::new(1);
  circuit.verify(&mut OsRng, &mut verifier, &mut transcript, proof);
  assert!(verifier.verify_vartime());
}

#[test]
fn test_dlog_pok() {
  let (g, h, g_bold1, g_bold2, h_bold1, h_bold2) = generators(64 * 256);
  let (additional_g_1, additional_g_2, additional_hs_1, additional_hs_2, _, _) =
    generators::<Vesta>(64 * 256);
  let additional_gs = (additional_g_1, additional_g_2);
  let additional_hs = (additional_hs_1.0.clone(), additional_hs_2.0.clone());

  let transcript = RecommendedTranscript::new(b"Point DLog PoK Circuit Test");

  let G_table = DLogTable::<Pallas>::new(<Pallas as Ciphersuite>::G::generator());

  let gadget = |circuit: &mut Circuit<Vesta>, point: (_, _), dlog: Vec<u8>| {
    let prover = circuit.prover();

    let point_x = circuit.add_secret_input(Some(point.0).filter(|_| prover));
    let point_y = circuit.add_secret_input(Some(point.1).filter(|_| prover));

    let point = <Vesta as EmbeddedCurveOperations>::constrain_on_curve(circuit, point_x, point_y);

    let mut bits = vec![];
    for bit in &dlog {
      bits.push(Bit::new_from_choice(circuit, Some((*bit).into()).filter(|_| prover)));
    }
    assert_eq!(u32::try_from(bits.len()).unwrap(), <Pallas as Ciphersuite>::F::CAPACITY);

    <Vesta as EmbeddedCurveOperations>::dlog_pok(&mut OsRng, circuit, &G_table, point, &bits);
  };

  let test = |point: (_, _), dlog: Vec<_>| {
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
    gadget(&mut circuit, point, dlog.clone());
    let (_, commitments, proof, proofs) = circuit.prove_with_vector_commitments(
      &mut OsRng,
      &mut transcript.clone(),
      additional_gs,
      additional_hs.clone(),
    );

    let mut circuit = Circuit::new(
      g,
      h,
      g_bold1.clone(),
      g_bold2.clone(),
      h_bold1.clone(),
      h_bold2.clone(),
      false,
      Some(commitments),
    );
    gadget(&mut circuit, point, dlog);

    let mut verifier = BatchVerifier::new(5);
    circuit.verify_with_vector_commitments(
      &mut OsRng,
      &mut verifier,
      &mut transcript.clone(),
      additional_gs,
      additional_hs.clone(),
      proof,
      proofs,
    );
    assert!(verifier.verify_vartime());
  };

  assert_eq!(<Pallas as Ciphersuite>::F::CAPACITY, <Vesta as Ciphersuite>::F::CAPACITY);

  {
    let point = <Pallas as Ciphersuite>::G::generator().to_affine().coordinates().unwrap();
    let point = (*point.x(), *point.y());

    let dlog = <Vesta as Ciphersuite>::F::ONE;
    let mut dlog = dlog.to_le_bits().iter().map(|bit| u8::from(*bit)).collect::<Vec<_>>();
    dlog.truncate(
      <Pallas as Ciphersuite>::F::CAPACITY
        .min(<Vesta as Ciphersuite>::F::CAPACITY)
        .try_into()
        .unwrap(),
    );

    test(point, dlog);
  }

  for _ in 0 .. 8 {
    let (dlog, bits) = loop {
      let dlog = <Pallas as Ciphersuite>::F::random(&mut OsRng);
      let mut bits = dlog.to_le_bits().iter().map(|bit| u8::from(*bit)).collect::<Vec<_>>();
      for bit in bits.iter().skip(<Pallas as Ciphersuite>::F::CAPACITY.try_into().unwrap()) {
        if *bit == 1 {
          continue;
        }
      }
      bits.truncate(
        <Pallas as Ciphersuite>::F::CAPACITY
          .min(<Vesta as Ciphersuite>::F::CAPACITY)
          .try_into()
          .unwrap(),
      );

      let mut count = 0;
      for bit in &bits {
        if *bit == 1 {
          count += 1;
        }
      }
      // TODO: Remove once the ecip lib supports odd amounts of points
      if (count % 2) != 1 {
        continue;
      }

      break (dlog, bits);
    };

    let point = (<Pallas as Ciphersuite>::G::generator() * dlog).to_affine().coordinates().unwrap();
    let point = (*point.x(), *point.y());

    test(point, bits);
  }

  // TODO: Test every bit being set
}
