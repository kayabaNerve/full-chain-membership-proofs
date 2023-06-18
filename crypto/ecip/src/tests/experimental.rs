use rand_core::OsRng;

use ciphersuite::{
  group::{ff::Field, Group},
  Ciphersuite, Pallas,
};

use crate::{Ecip, Divisor, experimental::*};

#[test]
fn test_dlog() {
  // Test with a divisor in case the "dlog" function is incomplete
  // Since it's meant to be used with divisors, any divisor passed should work
  let mut points = vec![<Pallas as Ciphersuite>::G::random(&mut OsRng)];
  points.push(-points.iter().sum::<<Pallas as Ciphersuite>::G>());
  let divisor = Divisor::<Pallas>::new(&points);

  dlog::<Pallas>(&divisor);
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

    let mut rhs = <Pallas as Ecip>::FieldElement::ZERO;
    for point in points {
      rhs += eval_challenge_against_point::<Pallas>(challenge, point);
    }
    assert_eq!(eval_challenge::<Pallas>(challenge, &divisor), rhs);
  }
}
