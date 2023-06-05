#![allow(non_snake_case)]

use ciphersuite::{
  group::{
    ff::{Field, PrimeField},
    Group,
  },
  Ciphersuite,
};

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

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Poly<F: Field> {
  // y ** (i + 1)
  pub y_coefficients: Vec<F>,
  // y ** (i + 1) x ** (j + 1)
  pub yx_coefficients: Vec<Vec<F>>,
  // x ** (i + 1)
  pub x_coefficients: Vec<F>,
  // Coefficient for x ** 0, y ** 0, and x ** 0 y ** 0
  pub zero_coefficient: F,
}

// TODO: This isn't constant time.
// The divisor calculation should be constant time w.r.t. the amount of points it's calculated
// for.
impl<F: Field> Poly<F> {
  fn zero() -> Self {
    Poly {
      y_coefficients: vec![],
      yx_coefficients: vec![],
      x_coefficients: vec![],
      zero_coefficient: F::ZERO,
    }
  }

  fn tidy(&mut self) {
    let tidy = |vec: &mut Vec<F>| {
      while vec.last() == Some(&F::ZERO) {
        vec.pop();
      }
    };

    tidy(&mut self.y_coefficients);
    for vec in self.yx_coefficients.iter_mut() {
      tidy(vec);
    }
    while self.yx_coefficients.last() == Some(&vec![]) {
      self.yx_coefficients.pop();
    }
    tidy(&mut self.x_coefficients);
  }

  fn add(mut self, other: &Self) -> Self {
    self.tidy();

    // Expand to be the neeeded size
    while self.y_coefficients.len() < other.y_coefficients.len() {
      self.y_coefficients.push(F::ZERO);
    }
    while self.yx_coefficients.len() < other.yx_coefficients.len() {
      self.yx_coefficients.push(vec![]);
    }
    for i in 0 .. other.yx_coefficients.len() {
      while self.yx_coefficients[i].len() < other.yx_coefficients[i].len() {
        self.yx_coefficients[i].push(F::ZERO);
      }
    }
    while self.x_coefficients.len() < other.x_coefficients.len() {
      self.x_coefficients.push(F::ZERO);
    }

    // Perform the subtraction
    for (i, coeff) in other.y_coefficients.iter().enumerate() {
      self.y_coefficients[i] += coeff;
    }
    for (i, coeffs) in other.yx_coefficients.iter().enumerate() {
      for (j, coeff) in coeffs.iter().enumerate() {
        self.yx_coefficients[i][j] += coeff;
      }
    }
    for (i, coeff) in other.x_coefficients.iter().enumerate() {
      self.x_coefficients[i] += coeff;
    }
    self.zero_coefficient += other.zero_coefficient;

    self.tidy();
    self
  }

  fn scale(mut self, scalar: F) -> Self {
    for y_coeff in self.y_coefficients.iter_mut() {
      *y_coeff *= scalar;
    }
    for coeffs in self.yx_coefficients.iter_mut() {
      for coeff in coeffs.iter_mut() {
        *coeff *= scalar;
      }
    }
    for x_coeff in self.x_coefficients.iter_mut() {
      *x_coeff *= scalar;
    }
    self.zero_coefficient *= scalar;
    self
  }

  fn sub(self, other: Self) -> Self {
    self.add(&other.scale(-F::ONE))
  }

  fn inner_mul(self, other: &Self) -> Self {
    let mut res =
      self.clone().scale(other.zero_coefficient).add(&other.clone().scale(self.zero_coefficient));
    // Because the zero coefficient term was applied twice, correct it
    res.zero_coefficient = self.zero_coefficient * other.zero_coefficient;

    fn same_scale<F: Field>(lhs: &[F], rhs: &[F], output: &mut Vec<F>) {
      for (pow_a, coeff_a) in rhs.iter().copied().enumerate().map(|(i, v)| (i + 1, v)) {
        for (pow_b, coeff_b) in lhs.iter().enumerate().map(|(i, v)| (i + 1, v)) {
          let pow_c = pow_a + pow_b;

          while output.len() < pow_c {
            output.push(F::ZERO);
          }
          output[pow_c - 1] += coeff_a * coeff_b;
        }
      }
    }
    fn add_yx<F: Field>(yx_coefficients: &mut Vec<Vec<F>>, y_pow: usize, x_pow: usize, coeff: F) {
      while yx_coefficients.len() < y_pow {
        yx_coefficients.push(vec![]);
      }
      while yx_coefficients[y_pow - 1].len() < x_pow {
        yx_coefficients[y_pow - 1].push(F::ZERO);
      }
      yx_coefficients[y_pow - 1][x_pow - 1] += coeff;
    }

    // Scale by y coefficients
    fn mul_by_y<F: Field>(first: bool, y_coefficients: &[F], other: &Poly<F>, res: &mut Poly<F>) {
      // y y
      if first {
        same_scale(y_coefficients, &other.y_coefficients, &mut res.y_coefficients);
      }

      // y yx
      for (y_pow_a, y_coeff) in y_coefficients.iter().copied().enumerate().map(|(i, v)| (i + 1, v))
      {
        for (y_pow_b, yx_coeffs) in
          other.yx_coefficients.iter().enumerate().map(|(i, v)| (i + 1, v))
        {
          let y_pow_c = y_pow_a + y_pow_b;
          for (x_pow, yx_coeff) in yx_coeffs.iter().enumerate().map(|(i, v)| (i + 1, v)) {
            add_yx(&mut res.yx_coefficients, y_pow_c, x_pow, y_coeff * yx_coeff);
          }
        }
      }

      // y x
      for (y_pow, y_coeff) in y_coefficients.iter().copied().enumerate().map(|(i, v)| (i + 1, v)) {
        for (x_pow, x_coeff) in other.x_coefficients.iter().enumerate().map(|(i, v)| (i + 1, v)) {
          add_yx(&mut res.yx_coefficients, y_pow, x_pow, y_coeff * x_coeff);
        }
      }
    }
    mul_by_y(true, &self.y_coefficients, other, &mut res);
    mul_by_y(false, &other.y_coefficients, &self, &mut res);

    // Scale by x coefficients
    fn mul_by_x<F: Field>(first: bool, x_coefficients: &[F], other: &Poly<F>, res: &mut Poly<F>) {
      // x x
      if first {
        same_scale(x_coefficients, &other.x_coefficients, &mut res.x_coefficients);
      }

      // x xy
      for (x_pow_a, coeff_a) in x_coefficients.iter().copied().enumerate().map(|(i, v)| (i + 1, v))
      {
        for (y_pow, yx_coeffs) in other.yx_coefficients.iter().enumerate().map(|(i, v)| (i + 1, v))
        {
          for (x_pow_b, coeff_b) in yx_coeffs.iter().enumerate().map(|(i, v)| (i + 1, v)) {
            let x_pow_c = x_pow_a + x_pow_b;
            add_yx(&mut res.yx_coefficients, y_pow, x_pow_c, coeff_a * coeff_b);
          }
        }
      }

      // Doesn't do x y since the prior function should have done that
    }
    mul_by_x(true, &self.x_coefficients, other, &mut res);
    mul_by_x(false, &other.x_coefficients, &self, &mut res);

    // The only thing left is the xy xy product
    for (y_pow_a, yx_coeffs_a) in other.yx_coefficients.iter().enumerate().map(|(i, v)| (i + 1, v))
    {
      for (x_pow_a, coeff_a) in yx_coeffs_a.iter().copied().enumerate().map(|(i, v)| (i + 1, v)) {
        for (y_pow_b, yx_coeffs_b) in
          self.yx_coefficients.iter().enumerate().map(|(i, v)| (i + 1, v))
        {
          for (x_pow_b, coeff_b) in yx_coeffs_b.iter().enumerate().map(|(i, v)| (i + 1, v)) {
            let y_pow_c = y_pow_a + y_pow_b;
            let x_pow_c = x_pow_a + x_pow_b;
            add_yx(&mut res.yx_coefficients, y_pow_c, x_pow_c, coeff_a * coeff_b);
          }
        }
      }
    }

    res.tidy();
    res
  }

  fn div_rem(self, denominator: &Self) -> (Self, Self) {
    let leading_y = |poly: &Self| -> (_, _) {
      if poly.y_coefficients.len() > poly.yx_coefficients.len() {
        (poly.y_coefficients.len(), 0)
      } else if !poly.yx_coefficients.is_empty() {
        (poly.yx_coefficients.len(), poly.yx_coefficients.last().unwrap().len())
      } else {
        (0, poly.x_coefficients.len())
      }
    };

    let leading_x = |poly: &Self| -> (_, _) {
      if poly.yx_coefficients.is_empty() {
        if !poly.x_coefficients.is_empty() {
          return (0, poly.x_coefficients.len());
        }
        return (poly.y_coefficients.len(), 0);
      }

      let mut longest_yx = 0;
      for i in 0 .. poly.yx_coefficients.len() {
        if poly.yx_coefficients[i].len() > poly.yx_coefficients[longest_yx].len() {
          longest_yx = i;
        }
      }

      if poly.x_coefficients.len() > poly.yx_coefficients[longest_yx].len() {
        (0, poly.x_coefficients.len())
      } else {
        (longest_yx + 1, poly.yx_coefficients[longest_yx].len())
      }
    };

    let y_denom = leading_y(denominator).0 != 0;

    let mut q = Poly::zero();
    let mut r = self;
    while {
      let ((y_a, x_a), (y_b, x_b)) = if y_denom {
        (leading_y(&r), leading_y(denominator))
      } else {
        (leading_x(&r), leading_x(denominator))
      };
      (r != Poly::zero()) && (y_a >= y_b) && (x_a >= x_b)
    } {
      let ((y_a, x_a), (y_b, x_b)) = if y_denom {
        (leading_y(&r), leading_y(denominator))
      } else {
        (leading_x(&r), leading_x(denominator))
      };

      let coeff = |poly: &Self, y: usize, x: usize| -> F {
        if (y == 0) && (x == 0) {
          poly.zero_coefficient
        } else if x == 0 {
          poly.y_coefficients[y - 1]
        } else if y == 0 {
          poly.x_coefficients[x - 1]
        } else {
          poly.yx_coefficients[y - 1][x - 1]
        }
      };

      let coeff_a = coeff(&r, y_a, x_a);
      let coeff_b = coeff(denominator, y_b, x_b);
      let coeff = coeff_a * Option::<F>::from(coeff_b.invert()).expect("denominator wasn't tidy");
      let y_c = y_a - y_b;
      let x_c = x_a - x_b;

      let mut t = Poly::zero();
      if (y_c == 0) && (x_c == 0) {
        t.zero_coefficient = coeff;
      } else if x_c == 0 {
        t.y_coefficients = vec![F::ZERO; y_c];
        t.y_coefficients[y_c - 1] = coeff;
      } else if y_c == 0 {
        t.x_coefficients = vec![F::ZERO; x_c];
        t.x_coefficients[x_c - 1] = coeff;
      } else {
        t.yx_coefficients = vec![vec![]; y_c];
        t.yx_coefficients[y_c - 1] = vec![F::ZERO; x_c];
        t.yx_coefficients[y_c - 1][x_c - 1] = coeff;
      }
      q = q.add(&t);
      r = r.sub(t.inner_mul(denominator));
    }

    (q, r)
  }

  // Compute the modulus via long division
  fn rem(self, modulus: &Self) -> Self {
    self.div_rem(modulus).1
  }

  fn mul(self, other: &Self, modulus: &Self) -> Self {
    self.inner_mul(other).rem(modulus)
  }

  pub fn eval(&self, x: F, y: F) -> F {
    let mut res = self.zero_coefficient;
    for (pow, coeff) in
      self.y_coefficients.iter().enumerate().map(|(i, v)| (u64::try_from(i + 1).unwrap(), v))
    {
      res += y.pow([pow]) * coeff;
    }
    for (y_pow, coeffs) in
      self.yx_coefficients.iter().enumerate().map(|(i, v)| (u64::try_from(i + 1).unwrap(), v))
    {
      let y_pow = y.pow([y_pow]);
      for (x_pow, coeff) in
        coeffs.iter().enumerate().map(|(i, v)| (u64::try_from(i + 1).unwrap(), v))
      {
        res += y_pow * x.pow([x_pow]) * coeff;
      }
    }
    for (pow, coeff) in
      self.x_coefficients.iter().enumerate().map(|(i, v)| (u64::try_from(i + 1).unwrap(), v))
    {
      res += x.pow([pow]) * coeff;
    }
    res
  }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Divisor<C: Ecip> {
  numerator: Poly<C::FieldElement>,
  denominator: Poly<C::FieldElement>,
}

impl<C: Ecip> Divisor<C> {
  fn initial(a: C::G, mut b: C::G) -> Self {
    if a == b {
      b = -a.double();
    }

    let (ax, ay) = C::to_xy(a);
    let (bx, by) = C::to_xy(b);

    Divisor {
      numerator: if (a + b) == C::G::identity() {
        // x (variable) - x (value)
        Poly {
          y_coefficients: vec![],
          yx_coefficients: vec![],
          x_coefficients: vec![C::FieldElement::ONE],
          zero_coefficient: -ax,
        }
      } else {
        let slope = (by - ay) * (bx - ax).invert().unwrap();
        let intercept = by - (slope * bx);

        // y - (slope * x) - intercept
        Poly {
          y_coefficients: vec![C::FieldElement::ONE],
          yx_coefficients: vec![],
          x_coefficients: vec![-slope],
          zero_coefficient: -intercept,
        }
      },
      denominator: Poly {
        y_coefficients: vec![],
        yx_coefficients: vec![],
        x_coefficients: vec![],
        zero_coefficient: C::FieldElement::ONE,
      },
    }
  }

  fn add(self, other: &Self, modulus: &Poly<C::FieldElement>) -> Self {
    let Divisor { numerator, denominator } = self;
    Self {
      numerator: numerator.mul(&other.numerator, modulus),
      denominator: denominator.mul(&other.denominator, modulus),
    }
  }

  fn sub(self, other: &Self, modulus: &Poly<C::FieldElement>) -> Self {
    let Divisor { numerator, denominator } = self;
    Self {
      numerator: numerator.mul(&other.denominator, modulus),
      denominator: denominator.mul(&other.numerator, modulus),
    }
  }

  #[allow(clippy::new_ret_no_self)]
  pub fn new(points: &[C::G]) -> Poly<C::FieldElement> {
    assert!(points.len() > 1);
    assert_eq!(points.len() % 2, 0); // TODO: Support odd numbers of points
    assert_eq!(points.iter().sum::<C::G>(), C::G::identity());

    let mut divs = vec![];
    let mut iter = points.iter().copied();
    while let Some(a) = iter.next() {
      let b = iter.next().unwrap();

      assert!(a != C::G::identity());
      assert!(b != C::G::identity());

      divs.push((a + b, Self::initial(a, b)));
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

    let mut res = divs.pop().unwrap();
    for div in divs {
      let (a, a_div) = res;
      let (b, b_div) = div;

      let c = Self::initial(a, b);
      res = (
        a + b,
        a_div
          .add(&b_div, &modulus)
          .add(&c, &modulus)
          .sub(&Self::initial(a, -a), &modulus)
          .sub(&Self::initial(b, -b), &modulus),
      );
    }

    let Divisor { numerator, denominator } = res.1;
    let (res, rem) = numerator.div_rem(&denominator);
    debug_assert_eq!(rem, Poly::zero());

    // This has to be asserted in circuit
    assert_eq!(*res.x_coefficients.last().unwrap(), C::FieldElement::ONE);

    res
  }
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
