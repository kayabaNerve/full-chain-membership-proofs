use ciphersuite::group::{ff::Field, Group};

use crate::*;

pub(crate) fn dlog<C: Ecip>(poly: &Poly<C::FieldElement>) -> Divisor<C> {
  let (dx, dy) = poly.differentiate();

  // Dz = Dx + Dy * ((3*x^2 + A) / (2*y))

  let dy_numerator = dy.inner_mul(&Poly {
    y_coefficients: vec![],
    yx_coefficients: vec![],
    x_coefficients: vec![C::FieldElement::ZERO, C::FieldElement::from(3)],
    zero_coefficient: C::FieldElement::from(C::A),
  });

  let denominator = Poly {
    y_coefficients: vec![C::FieldElement::from(2)],
    yx_coefficients: vec![],
    x_coefficients: vec![],
    zero_coefficient: C::FieldElement::ZERO,
  };

  let numerator = dx.inner_mul(&denominator).add(&dy_numerator);

  // Dz is numerator / denominator
  // Dz / D
  let denominator = denominator.inner_mul(poly);

  // TODO: We have two polys. Can we shrink their combined side by dividing the numerator by the
  // denominator's x terms, instead of by the y terms?

  let modulus = Poly {
    y_coefficients: vec![C::FieldElement::ZERO, C::FieldElement::ONE],
    yx_coefficients: vec![],
    x_coefficients: vec![
      -C::FieldElement::from(C::A),
      C::FieldElement::ZERO,
      -C::FieldElement::ONE,
    ],
    zero_coefficient: -C::FieldElement::from(C::B),
  };

  Divisor { numerator: numerator.rem(&modulus), denominator: denominator.rem(&modulus) }
}

pub(crate) fn eval_challenge<C: Ecip>(
  challenge: C::G,
  divisor: &Poly<C::FieldElement>,
) -> C::FieldElement {
  let dlog = dlog::<C>(divisor);

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

  let mut dlog_left = dlog.clone();
  dlog_left.numerator = dlog_left.numerator.scale(coeff0);
  let left =
    dlog_left.numerator.eval(cx, cy) * dlog_left.denominator.eval(cx, cy).invert().unwrap();

  let mut dlog_right = dlog;
  dlog_right.numerator = dlog_right.numerator.scale(coeff2);
  let right =
    dlog_right.numerator.eval(dx, dy) * dlog_right.denominator.eval(dx, dy).invert().unwrap();

  left - right
}

pub(crate) fn eval_challenge_against_point<C: Ecip>(
  challenge: C::G,
  point: C::G,
) -> C::FieldElement {
  let (slope, intercept) = slope_intercept::<C>(challenge, -challenge.double());

  let cx = C::to_xy(challenge).0;
  let (px, py) = C::to_xy(point);

  (cx - px) * (py - (slope * px) - intercept).invert().unwrap()
}
