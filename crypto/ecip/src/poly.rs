use ciphersuite::group::ff::Field;

use crate::{Ecip, Divisor};

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
  pub(crate) fn zero() -> Self {
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
  pub(crate) fn tidy(&mut self) {
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
  pub(crate) fn add(mut self, other: &Self) -> Self {
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
  pub(crate) fn scale(mut self, scalar: F) -> Self {
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
  pub(crate) fn sub(self, other: Self) -> Self {
    self.add(&other.scale(-F::ONE))
  }

  // Perform a mul without performing a reduction
  pub(crate) fn inner_mul(self, other: &Self) -> Self {
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
  pub(crate) fn div_rem(self, denominator: &Self) -> (Self, Self) {
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
  pub(crate) fn rem(self, modulus: &Self) -> Self {
    self.div_rem(modulus).1
  }

  // Perform multiplication mod modulus
  pub(crate) fn mul(self, other: &Self, modulus: &Self) -> Self {
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
    assert!(self.y_coefficients.len() <= 1);
    assert!(self.yx_coefficients.len() <= 1);
    let diff_y = Poly {
      y_coefficients: vec![],
      yx_coefficients: vec![],
      x_coefficients: self.yx_coefficients.get(0).cloned().unwrap_or(vec![]),
      zero_coefficient: self.y_coefficients.get(0).cloned().unwrap_or(F::ZERO),
    };

    (diff_x, diff_y)
  }

  /// Normalize the x coefficient to 1.
  pub fn normalize_x_coefficient(self) -> Self {
    let scalar = self.x_coefficients[0].invert().unwrap();
    self.scale(scalar)
  }

  // Calculate the logarithmic derivative of a polynomial.
  pub fn logarithmic_derivative<C: Ecip<FieldElement = F>>(&self) -> Divisor<C> {
    let (dx, dy) = self.differentiate();

    // Dz = Dx + (Dy * ((3*x^2 + A) / (2*y)))

    let dy_numerator = dy.inner_mul(&Poly {
      y_coefficients: vec![],
      yx_coefficients: vec![],
      x_coefficients: vec![F::ZERO, F::from(3)],
      zero_coefficient: F::from(C::A),
    });

    let denominator = Poly {
      y_coefficients: vec![F::from(2)],
      yx_coefficients: vec![],
      x_coefficients: vec![],
      zero_coefficient: F::ZERO,
    };

    let numerator = dx.inner_mul(&denominator).add(&dy_numerator);

    // Dz is numerator / denominator
    // Dz / D
    let denominator = denominator.inner_mul(self);

    let modulus = Poly {
      y_coefficients: vec![F::ZERO, F::ONE],
      yx_coefficients: vec![],
      x_coefficients: vec![-F::from(C::A), F::ZERO, -F::ONE],
      zero_coefficient: -F::from(C::B),
    };

    let numerator = numerator.rem(&modulus);
    let denominator = denominator.rem(&modulus);

    assert_eq!(numerator.y_coefficients.len(), 1);
    assert_eq!(denominator.y_coefficients.len(), 1);

    Divisor { numerator, denominator }
  }
}
