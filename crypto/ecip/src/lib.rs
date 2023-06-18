#![allow(non_snake_case)]

use ciphersuite::{
  group::{
    ff::{Field, PrimeField},
    Group,
  },
  Ciphersuite,
};

mod poly;
pub use poly::*;

pub(crate) mod experimental;

#[cfg(test)]
pub(crate) mod tests;

pub trait Ecip: Ciphersuite {
  type FieldElement: PrimeField;

  const A: u64;
  const B: u64;

  fn to_xy(point: Self::G) -> (Self::FieldElement, Self::FieldElement);
  /// Panics if off-curve.
  // This isn't used in-lib, yet is helpful to users
  fn from_xy(x: Self::FieldElement, y: Self::FieldElement) -> Self::G;

  // Required to securely generate challenge points.
  fn hash_to_G(domain: &'static str, data: &[u8]) -> Self::G;
}

fn slope_intercept<C: Ecip>(a: C::G, b: C::G) -> (C::FieldElement, C::FieldElement) {
  let (ax, ay) = C::to_xy(a);
  let (bx, by) = C::to_xy(b);
  let slope = (by - ay) *
    Option::<C::FieldElement>::from((bx - ax).invert())
      .expect("trying to get slope/intercept of points sharing an x coordinate");
  let intercept = by - (slope * bx);
  debug_assert!(bool::from((ay - (slope * ax) - intercept).is_zero()));
  debug_assert!(bool::from((by - (slope * bx) - intercept).is_zero()));
  (slope, intercept)
}

/// Constructor of a divisor (represented via a Poly) for a set of elliptic curve point.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Divisor<C: Ecip> {
  numerator: Poly<C::FieldElement>,
  denominator: Poly<C::FieldElement>,
}

impl<C: Ecip> Divisor<C> {
  // TODO: Is this complete? Or will it return garbage in some cases?
  fn line(a: C::G, mut b: C::G) -> Self {
    let (ax, _) = C::to_xy(a);

    if (a + b) == C::G::identity() {
      return Divisor {
        numerator: Poly {
          y_coefficients: vec![],
          yx_coefficients: vec![],
          x_coefficients: vec![C::FieldElement::ONE],
          zero_coefficient: -ax,
        },
        denominator: Poly {
          y_coefficients: vec![],
          yx_coefficients: vec![],
          x_coefficients: vec![],
          zero_coefficient: C::FieldElement::ONE,
        },
      };
    }

    if a == b {
      b = -a.double();
    }

    let (slope, intercept) = slope_intercept::<C>(a, b);

    // y - (slope * x) - intercept
    Divisor {
      numerator: Poly {
        y_coefficients: vec![C::FieldElement::ONE],
        yx_coefficients: vec![],
        x_coefficients: vec![-slope],
        zero_coefficient: -intercept,
      },
      denominator: Poly {
        y_coefficients: vec![],
        yx_coefficients: vec![],
        x_coefficients: vec![],
        zero_coefficient: C::FieldElement::ONE,
      },
    }
  }

  fn mul(self, other: &Self, modulus: &Poly<C::FieldElement>) -> Self {
    let Divisor { numerator, denominator } = self;
    Self {
      numerator: numerator.mul(&other.numerator, modulus),
      denominator: denominator.mul(&other.denominator, modulus),
    }
  }

  fn div(self, other: &Self, modulus: &Poly<C::FieldElement>) -> Self {
    let Divisor { numerator, denominator } = self;
    Self {
      numerator: numerator.mul(&other.denominator, modulus),
      denominator: denominator.mul(&other.numerator, modulus),
    }
  }

  /// Create a divisor interpolating the following points.
  #[allow(clippy::new_ret_no_self)]
  pub fn new(points: &[C::G]) -> Poly<C::FieldElement> {
    assert!(points.len() > 1);
    assert_eq!(points.len() % 2, 0); // TODO: Support odd numbers of points
    assert_eq!(points.iter().sum::<C::G>(), C::G::identity());

    let mut divs = vec![];
    let mut iter = points.iter().copied();
    while let Some(a) = iter.next() {
      let b = iter.next();

      assert!(a != C::G::identity());
      if let Some(b) = b {
        assert!(b != C::G::identity());
      }

      divs.push((a + b.unwrap_or(C::G::identity()), Self::line(a, b.unwrap_or(-a))));
    }

    // y^2 - x^3 - Ax - B
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

    while divs.len() > 1 {
      let mut next_divs = vec![];
      if (divs.len() % 2) == 1 {
        next_divs.push(divs.pop().unwrap());
      }

      while let Some((a, a_div)) = divs.pop() {
        let (b, b_div) = divs.pop().unwrap();

        next_divs.push((
          a + b,
          a_div
            .mul(&b_div, &modulus)
            .mul(&Self::line(a, b), &modulus)
            .div(&Self::line(a, -a).mul(&Self::line(b, -b), &modulus), &modulus),
        ));
      }

      divs = next_divs;
    }

    let Divisor { numerator, denominator } = divs.remove(0).1;
    let (res, rem) = numerator.div_rem(&denominator);
    debug_assert_eq!(rem, Poly::zero());

    // This has to be asserted in circuit
    assert_eq!(*res.x_coefficients.last().unwrap(), C::FieldElement::ONE);

    res
  }

  /*
  // FieldElement divisor.
  // Rearranges Product(xi) to a polynomial F(x), where F(x) = Product(x + xi).
  // This is notable as the polynomial evaluation can happen via constraints, without adding gates.
  #[allow(clippy::new_ret_no_self)]
  pub fn new_fe(fes: &[C::FieldElement]) -> Poly<C::FieldElement> {
    assert!(!fes.is_empty());

    let mut res = Poly {
      y_coefficients: vec![],
      yx_coefficients: vec![],
      x_coefficients: vec![],
      zero_coefficient: C::FieldElement::ONE,
    };
    for fe in fes {
      res = res.mul(
        &Poly {
          y_coefficients: vec![],
          yx_coefficients: vec![],
          x_coefficients: vec![C::FieldElement::ONE],
          zero_coefficient: *fe,
        },
        // Use a modulus with a y coefficient so no reduction occurs
        &Poly {
          y_coefficients: vec![C::FieldElement::ONE],
          yx_coefficients: vec![],
          x_coefficients: vec![],
          zero_coefficient: C::FieldElement::ZERO,
        },
      );
    }
    res
  }
  */
}

#[cfg(any(test, feature = "pasta"))]
mod pasta {
  use pasta_curves::arithmetic::{Coordinates, CurveAffine, CurveExt};
  use ciphersuite::{
    group::{ff::Field, Curve},
    Ciphersuite, Pallas, Vesta,
  };

  use crate::Ecip;

  impl Ecip for Pallas {
    type FieldElement = <Vesta as Ciphersuite>::F;

    const A: u64 = 0;
    const B: u64 = 5;

    fn from_xy(x: Self::FieldElement, y: Self::FieldElement) -> Self::G {
      pasta_curves::pallas::Affine::from_xy(x, y).unwrap().into()
    }

    fn to_xy(
      point: <Pallas as Ciphersuite>::G,
    ) -> (<Vesta as Ciphersuite>::F, <Vesta as Ciphersuite>::F) {
      Option::<Coordinates<_>>::from(point.to_affine().coordinates())
        .map(|coords| (*coords.x(), *coords.y()))
        .unwrap_or((<Vesta as Ciphersuite>::F::ZERO, <Vesta as Ciphersuite>::F::ZERO))
    }

    fn hash_to_G(domain: &str, data: &[u8]) -> Self::G {
      <Pallas as Ciphersuite>::G::hash_to_curve(domain)(data)
    }
  }

  impl Ecip for Vesta {
    type FieldElement = <Pallas as Ciphersuite>::F;

    const A: u64 = 0;
    const B: u64 = 5;

    fn from_xy(x: Self::FieldElement, y: Self::FieldElement) -> Self::G {
      pasta_curves::vesta::Affine::from_xy(x, y).unwrap().into()
    }

    fn to_xy(
      point: <Vesta as Ciphersuite>::G,
    ) -> (<Pallas as Ciphersuite>::F, <Pallas as Ciphersuite>::F) {
      Option::<Coordinates<_>>::from(point.to_affine().coordinates())
        .map(|coords| (*coords.x(), *coords.y()))
        .unwrap_or((<Pallas as Ciphersuite>::F::ZERO, <Pallas as Ciphersuite>::F::ZERO))
    }

    fn hash_to_G(domain: &str, data: &[u8]) -> Self::G {
      <Vesta as Ciphersuite>::G::hash_to_curve(domain)(data)
    }
  }
}
