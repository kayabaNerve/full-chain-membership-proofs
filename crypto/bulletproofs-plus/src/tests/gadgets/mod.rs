use rand_core::OsRng;

use transcript::{Transcript, RecommendedTranscript};

use multiexp::BatchVerifier;
use ciphersuite::{group::ff::Field, Ciphersuite, Vesta};

use crate::{arithmetic_circuit::Circuit, gadgets::is_non_zero_gadget, tests::generators};

mod elliptic_curve;

#[test]
fn test_is_non_zero_gadget() {
  let (g, h, g_bold1, g_bold2, h_bold1, h_bold2) = generators(16);

  fn gadget(circuit: &mut Circuit<Vesta>, value_arg: Option<<Vesta as Ciphersuite>::F>) {
    let value = circuit.add_secret_input(value_arg);
    circuit.product(value, value);
    let res = is_non_zero_gadget(circuit, value);
    if let Some(value) = value_arg {
      assert_eq!(
        circuit.unchecked_value(res.variable).unwrap(),
        if value == <Vesta as Ciphersuite>::F::ZERO {
          <Vesta as Ciphersuite>::F::ZERO
        } else {
          <Vesta as Ciphersuite>::F::ONE
        }
      );
    }
  }

  let transcript = RecommendedTranscript::new(b"Is Non Zero Gadget Test");

  let test = |x| {
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
    gadget(&mut circuit, Some(x));
    let proof = circuit.prove(&mut OsRng, &mut transcript.clone());

    let mut circuit = Circuit::new(
      g,
      h,
      g_bold1.clone(),
      g_bold2.clone(),
      h_bold1.clone(),
      h_bold2.clone(),
      false,
      Some(vec![]),
    );
    gadget(&mut circuit, None);
    let mut verifier = BatchVerifier::new(1);
    circuit.verify(&mut OsRng, &mut verifier, &mut transcript.clone(), proof);
    assert!(verifier.verify_vartime());
  };

  test(<Vesta as Ciphersuite>::F::ZERO);
  test(<Vesta as Ciphersuite>::F::ONE);
  test(<Vesta as Ciphersuite>::F::random(&mut OsRng));
}
