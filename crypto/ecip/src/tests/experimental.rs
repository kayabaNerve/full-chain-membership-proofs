use rand_core::OsRng;

use ciphersuite::{
  group::{ff::Field, Group},
  Ciphersuite, Pallas,
};

use crate::{Ecip, Divisor, experimental::*};

#[test]
fn test_three_two_eval() {
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

    // 3.2 z check
    {
      let challenge2 = <Pallas as Ciphersuite>::G::random(&mut OsRng);
      let (x, y) = <Pallas as Ecip>::to_xy(challenge);
      let (x2, y2) = <Pallas as Ecip>::to_xy(challenge2);
      let (x3, y3) = <Pallas as Ecip>::to_xy(-(challenge + challenge2));
      let lhs = divisor.eval(x, y) * divisor.eval(x2, y2) * divisor.eval(x3, y3);

      let (slope, intercept) = crate::slope_intercept::<Pallas>(challenge, challenge2);
      let mut rhs = <Pallas as Ecip>::FieldElement::ONE;
      for point in &points {
        let (x, y) = <Pallas as Ecip>::to_xy(*point);
        rhs *= intercept - (y - (slope * x));
      }
      assert_eq!(lhs, rhs);
    }

    let mut log_deriv = divisor.logarithmic_derivative();
    assert_eq!(log_deriv.numerator.y_coefficients.len(), 1);

    // Supposedly, the bottom formula from 3.2, yet this doesn't directly line up
    {
      let mut rhs = <Pallas as Ecip>::FieldElement::ZERO;
      for point in &points {
        rhs += eval_challenge_against_point_three_two::<Pallas>(challenge, *point);
      }
      assert_eq!(eval_challenge_three_two::<Pallas>(challenge, log_deriv.clone()), rhs);
    }

    // Normalize so the y coefficient is 1
    // This allows checking the divisor isn't 0
    normalize_y_coefficient(&mut log_deriv);
    assert_eq!(log_deriv.numerator.y_coefficients, vec![<Pallas as Ecip>::FieldElement::ONE]);
    {
      let mut rhs = <Pallas as Ecip>::FieldElement::ZERO;
      for point in points {
        rhs += eval_challenge_against_point_three_two::<Pallas>(challenge, point);
      }
      assert_eq!(eval_challenge_three_two::<Pallas>(challenge, log_deriv), rhs);
    }
  }
}
