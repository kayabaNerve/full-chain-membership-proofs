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

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Poly<F: Field + From<u64>> {
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
// for
impl<F: Field + From<u64>> Poly<F> {
  // A zero/empty polynomial.
  fn zero() -> Self {
    Poly {
      y_coefficients: vec![],
      yx_coefficients: vec![],
      x_coefficients: vec![],
      zero_coefficient: F::ZERO,
    }
  }

  /// Get the amount of non-zero terms in a polynomial.
  #[allow(clippy::len_without_is_empty)]
  pub fn len(&self) -> usize {
    self.y_coefficients.len() +
      self.yx_coefficients.iter().map(Vec::len).sum::<usize>() +
      self.x_coefficients.len() +
      usize::from(u8::from(self.zero_coefficient != F::ZERO))
  }

  // Remove high-order zero terms, allowing the length of vectors to equal the amount of terms.
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

  // Add two polynomials together
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

    // Perform the addition
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

  // Scale a polynomial by some scalar
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

  // Subtract a polynomial from this one
  fn sub(self, other: Self) -> Self {
    self.add(&other.scale(-F::ONE))
  }

  // Perform a mul without performing a reduction
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
    fn mul_by_y<F: Field + From<u64>>(
      first: bool,
      y_coefficients: &[F],
      other: &Poly<F>,
      res: &mut Poly<F>,
    ) {
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
    fn mul_by_x<F: Field + From<u64>>(
      first: bool,
      x_coefficients: &[F],
      other: &Poly<F>,
      res: &mut Poly<F>,
    ) {
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

  // Perform division, returning the result and remainder
  // This is incomplete, apparently in undocumented ways
  // It should be incomplete for any denominator with just a zero coefficient, and otherwise
  // complete
  // TODO: Confirm and document exactly how this is complete/incomplete
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

  // Perform multiplication mod modulus
  fn mul(self, other: &Self, modulus: &Self) -> Self {
    self.inner_mul(other).rem(modulus)
  }

  /// Evaluate this polynomial with the specified x/y values.
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

  /// Differentiate a polynomial, reduced y**2, by x and y.
  pub fn differentiate(&self) -> (Poly<F>, Poly<F>) {
    assert!(self.yx_coefficients.len() <= 1);
    assert!(self.y_coefficients.len() <= 1);

    // Differentation by x practically involves:
    // - Dropping everything without an x component
    // - Shifting everything down a power of x
    // - If the x power is greater than 2, multiplying the new term's coefficient by the x power in
    //   question
    let mut diff_x = Poly {
      y_coefficients: vec![],
      yx_coefficients: vec![],
      x_coefficients: vec![],
      zero_coefficient: F::ZERO,
    };
    diff_x.zero_coefficient = self.x_coefficients.get(0).cloned().unwrap_or(F::ZERO);
    for i in 1 .. self.x_coefficients.len() {
      let power = i + 1;
      diff_x.x_coefficients.push(self.x_coefficients[i] * F::from(u64::try_from(power).unwrap()));
    }

    for (i, yx_coeff) in
      self.yx_coefficients.get(0).cloned().unwrap_or(vec![]).into_iter().enumerate()
    {
      // Keep the y power, reduce an x power
      let power = i + 1;
      if i == 0 {
        diff_x.y_coefficients.push(yx_coeff);
      } else {
        if diff_x.yx_coefficients.is_empty() {
          diff_x.yx_coefficients.push(vec![]);
        }
        diff_x.yx_coefficients[0].push(yx_coeff * F::from(u64::try_from(power).unwrap()));
      }
    }

    // Differentation by y is trivial
    // It's the y coefficient as the zero coefficient, and the yx coefficients as the x coefficient
    // This is thanks to any y term over y^2 being reduced out
    let diff_y = Poly {
      y_coefficients: vec![],
      yx_coefficients: vec![],
      x_coefficients: self.yx_coefficients.get(0).cloned().unwrap_or(vec![]),
      zero_coefficient: self.y_coefficients.get(0).cloned().unwrap_or(F::ZERO),
    };

    (diff_x, diff_y)
  }
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

pub(crate) mod experimental {
  use super::*;

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
