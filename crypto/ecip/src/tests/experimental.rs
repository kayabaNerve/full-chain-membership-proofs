use rand_core::OsRng;

use ciphersuite::{
  group::{ff::Field, Group},
  Ciphersuite, Pallas,
};

use crate::{Ecip, Divisor, experimental::*};

#[test]
fn test_log_deriv() {
  // Test with a divisor in case the Logarithmic derivative function is incomplete
  // Since it's meant to be used with divisors, any divisor passed should work
  let mut points = vec![<Pallas as Ciphersuite>::G::random(&mut OsRng)];
  points.push(-points.iter().sum::<<Pallas as Ciphersuite>::G>());
  let divisor = Divisor::<Pallas>::new(&points);

  log_deriv::<Pallas>(&divisor);
}

#[test]
fn test_experimental_eval() {
  for i in 0 .. 256 {
    if (i % 2) != 1 {
      continue;
    }
    let mut points = vec![];
    for _ in 0 .. i {
      points.push(<Pallas as Ciphersuite>::G::random(&mut OsRng));
    }
    points.push(-points.iter().sum::<<Pallas as Ciphersuite>::G>());
    let divisor = Divisor::<Pallas>::new(&points);

    let challenge = <Pallas as Ciphersuite>::G::random(&mut OsRng);

    let mut log_deriv = log_deriv::<Pallas>(&divisor);
    assert_eq!(log_deriv.numerator.y_coefficients.len(), 1);

    {
      let mut rhs = <Pallas as Ecip>::FieldElement::ZERO;
      for point in &points {
        rhs += eval_challenge_against_point::<Pallas>(challenge, *point);
      }
      assert_eq!(eval_challenge::<Pallas>(challenge, log_deriv.clone()), rhs);
    }

    // Normalize so the y coefficient is 1
    // This allows checking the divisor isn't 0
    normalize_y_coefficient(&mut log_deriv);
    assert_eq!(log_deriv.numerator.y_coefficients, vec![<Pallas as Ecip>::FieldElement::ONE]);
    {
      let mut rhs = <Pallas as Ecip>::FieldElement::ZERO;
      for point in points {
        rhs += eval_challenge_against_point::<Pallas>(challenge, point);
      }
      assert_eq!(eval_challenge::<Pallas>(challenge, log_deriv), rhs);
    }
  }
}
