use ciphersuite::group::{ff::Field, Group};

use crate::*;

/*
pub fn get_polys<F: Field>(poly: &Poly<F>) -> (Poly<F>, Poly<F>) {
  let decomposition = Poly {
    y_coefficients,
    yx_coefficients,
    x_coefficients,
    zero_coefficient
  } = poly;

  // True if reduced by the curve equation
  assert!(yx_coefficients.len() <= 1);
  assert!(y_coefficients.len() <= 1);

  (
    // Poly(y = 0)
    Poly {
      y_coefficients: vec![],
      yx_coefficients: vec![],
      x_coefficients,
      zero_coefficient
    },
    // The second poly is poly(y = 1) - poly(y = 0)
    // This equates to the yx_coefficients as the x_coefficients, with the y_coefficient as the
    // zero_coefficient
    Poly {
      y_coefficients: vec![],
      yx_coefficients: vec![],
      x_coefficients: yx_coefficients.get(0).unwrap_or(vec![]),
      zero_coefficient: y_coefficients.get(0).unwrap_or(F::ZERO),
    }
  )
}
*/

/// Normalize the y coefficient to one.
// The logarithmic derivative of a divisor always has a y coefficient in the numerator and divisor,
// yet it doesn't always have x coefficients. Their zero coefficient will also be zero, when we
// need it to be one.
pub fn normalize_y_coefficient<C: Ecip>(divisor: &mut Divisor<C>) {
  let scalar = divisor.numerator.y_coefficients[0].invert().unwrap();
  divisor.numerator = divisor.numerator.clone().scale(scalar);
  divisor.denominator = divisor.denominator.clone().scale(scalar);
}

// Supposedly the bottom line of 3.2, yet this doesn't exactly line up
pub(crate) fn eval_challenge_three_two<C: Ecip>(
  challenge: C::G,
  log_deriv: Divisor<C>,
) -> C::FieldElement {
  let neg_dbl = -challenge.double();
  let (slope, _) = slope_intercept::<C>(challenge, neg_dbl);

  let (cx, cy) = C::to_xy(challenge);
  let (dx, dy) = C::to_xy(neg_dbl);

  let coeff2 = dy.double() *
    (cx - dx) *
    ((C::FieldElement::from(3) * dx.square()) + C::FieldElement::from(C::A) -
      (slope.double() * dy))
      .invert()
      .unwrap();
  let coeff0 = coeff2 + slope.double();

  let mut log_deriv_left = log_deriv.clone();
  log_deriv_left.numerator = log_deriv_left.numerator.scale(coeff0);
  let left = log_deriv_left.numerator.eval(cx, cy) *
    log_deriv_left.denominator.eval(cx, cy).invert().unwrap();

  let mut log_deriv_right = log_deriv;
  log_deriv_right.numerator = log_deriv_right.numerator.scale(coeff2);
  let right = log_deriv_right.numerator.eval(dx, dy) *
    log_deriv_right.denominator.eval(dx, dy).invert().unwrap();

  left - right
}

// Supposedly the bottom line of 3.2, yet this doesn't exactly line up
pub(crate) fn eval_challenge_against_point_three_two<C: Ecip>(
  challenge: C::G,
  point: C::G,
) -> C::FieldElement {
  let (slope, intercept) = slope_intercept::<C>(challenge, -challenge.double());

  let cx = C::to_xy(challenge).0;
  let (px, py) = C::to_xy(point);

  (cx - px) * (py - (slope * px) - intercept).invert().unwrap()
}
