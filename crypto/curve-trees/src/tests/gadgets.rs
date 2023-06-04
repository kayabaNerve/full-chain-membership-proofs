use rand_core::OsRng;

use transcript::{Transcript, RecommendedTranscript};
use ciphersuite::{group::ff::Field, Ciphersuite, Vesta};

use bulletproofs_plus::{arithmetic_circuit::Circuit, tests::generators};

use crate::gadgets::find_index_gadget;

#[test]
fn test_find_index_gadget() {
  let (g, h, g_bold1, g_bold2, h_bold1, h_bold2) = generators(64);

  fn gadget(
    circuit: &mut Circuit<Vesta>,
    value_arg: Option<<Vesta as Ciphersuite>::F>,
    values_arg: &[Option<<Vesta as Ciphersuite>::F>],
  ) {
    let value = circuit.add_secret_input(value_arg);
    circuit.product(value, value);

    let mut values = vec![];
    for value in values_arg {
      let value = circuit.add_secret_input(*value);
      circuit.product(value, value);
      values.push(value);
    }
    let res = find_index_gadget(circuit, value, &values);
    if let Some(value) = value_arg {
      for (i, value_i) in values_arg.iter().enumerate() {
        if value_i.unwrap() == value {
          assert_eq!(
            circuit.unchecked_value(res).unwrap(),
            <Vesta as Ciphersuite>::F::from(u64::try_from(i).unwrap())
          );
          break;
        }
      }
    }
  }

  let transcript = RecommendedTranscript::new(b"Find Index Gadget Test");

  let test = |x, xs: &[_]| {
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
    gadget(&mut circuit, Some(x), &xs.iter().map(|x| Some(*x)).collect::<Vec<_>>());
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
    gadget(&mut circuit, None, &xs.iter().map(|_| None).collect::<Vec<_>>());
    circuit.verify(&mut transcript.clone(), proof);
  };

  let mut values = vec![<Vesta as Ciphersuite>::F::random(&mut OsRng)];
  test(values[0], &values);
  values.push(<Vesta as Ciphersuite>::F::random(&mut OsRng));
  test(values[0], &values);
  test(values[1], &values);
  values.push(<Vesta as Ciphersuite>::F::random(&mut OsRng));
  test(values[0], &values);
  test(values[1], &values);
  test(values[2], &values);
}
