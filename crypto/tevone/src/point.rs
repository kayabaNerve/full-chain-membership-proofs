use core::{
  ops::{DerefMut, Add, AddAssign, Neg, Sub, SubAssign, Mul, MulAssign},
  iter::Sum,
};

use rand_core::RngCore;

use zeroize::Zeroize;
use subtle::{Choice, CtOption, ConstantTimeEq, ConditionallySelectable, ConditionallyNegatable};

use crypto_bigint::{U256, modular::constant_mod::Residue};

use group::{
  ff::{Field, PrimeField, PrimeFieldBits},
  Group, GroupEncoding,
  prime::PrimeGroup,
};

use crate::{backend::u8_from_bool, smaller::SmallerElement, larger::LargerElement};

macro_rules! curve {
  (
    $Scalar: ident,
    $Field: ident,
    $Point: ident,
    $G_X: literal,
    $G_Y: literal,
  ) => {
    const G_X: $Field = $Field(Residue::new(&U256::from_be_hex($G_X)));
    const G_Y: $Field = $Field(Residue::new(&U256::from_be_hex($G_Y)));

    const B: $Field = $Field(Residue::new(&U256::from_u8(97)));

    fn recover_y(x: $Field) -> CtOption<$Field> {
      ((x.square() * x) + B).sqrt()
    }

    /// Point.
    #[derive(Clone, Copy, Debug, Zeroize)]
    pub struct $Point {
      x: $Field, // / Z ** 2
      y: $Field, // / Z ** 3
      z: $Field,
    }

    const G: $Point = $Point { x: G_X, y: G_Y, z: $Field::ONE };

    impl ConstantTimeEq for $Point {
      fn ct_eq(&self, other: &Self) -> Choice {
        let z1z1 = self.z.square();
        let z2z2 = other.z.square();

        let x1 = self.x * z2z2;
        let x2 = other.x * z1z1;

        let y1 = self.y * z2z2 * other.z;
        let y2 = other.y * z1z1 * self.z;

        (self.x.is_zero() & other.x.is_zero()) | (x1.ct_eq(&x2) & y1.ct_eq(&y2))
      }
    }

    impl PartialEq for $Point {
      fn eq(&self, other: &$Point) -> bool {
        self.ct_eq(other).into()
      }
    }

    impl Eq for $Point {}

    impl ConditionallySelectable for $Point {
      fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        $Point {
          x: $Field::conditional_select(&a.x, &b.x, choice),
          y: $Field::conditional_select(&a.y, &b.y, choice),
          z: $Field::conditional_select(&a.z, &b.z, choice),
        }
      }
    }

    impl Add for $Point {
      type Output = $Point;
      fn add(self, other: Self) -> Self {
        let double = self.double();

        // add-2007-bl
        let mixed = {
          let z1z1 = self.z.square();
          let z2z2 = other.z.square();
          let u1 = self.x * z2z2;
          let u2 = other.x * z1z1;
          let s1 = self.y * other.z * z2z2;
          let s2 = other.y * self.z * z1z1;
          let h = u2 - u1;
          let i = h.double().square();
          let j = h * i;
          let r = (s2 - s1).double();
          let v = u1 * i;
          let x3 = r.square() - j - v.double();
          let y3 = (r * (v - x3)) - (s1.double() * j);
          let z3 = ((self.z + other.z).square() - z1z1 - z2z2) * h;

          $Point { x: x3, y: y3, z: z3 }
        };

        let self_is_identity = self.is_identity();
        let other_is_identity = other.is_identity();

        // Select the other point if self is identity
        // This may still be identity if both are identity. That just isn't an issue
        let non_identity = $Point::conditional_select(&self, &other, self_is_identity);
        // Select the double if they're equal
        let mixed_or_double = $Point::conditional_select(&mixed, &double, self.ct_eq(&other));
        // If one was identity, select the one which wasn't. Else, select the addition result
        let res = $Point::conditional_select(
          &mixed_or_double,
          &non_identity,
          self_is_identity | other_is_identity,
        );

        // If one was the other's negation, return identity
        $Point::conditional_select(&res, &Self::identity(), (-self).ct_eq(&other))
      }
    }

    impl AddAssign for $Point {
      fn add_assign(&mut self, other: $Point) {
        *self = *self + other;
      }
    }

    impl Add<&$Point> for $Point {
      type Output = $Point;
      fn add(self, other: &$Point) -> $Point {
        self + *other
      }
    }

    impl AddAssign<&$Point> for $Point {
      fn add_assign(&mut self, other: &$Point) {
        *self += *other;
      }
    }

    impl Neg for $Point {
      type Output = $Point;
      fn neg(self) -> Self {
        $Point { x: self.x, y: -self.y, z: self.z }
      }
    }

    impl Sub for $Point {
      type Output = $Point;
      #[allow(clippy::suspicious_arithmetic_impl)]
      fn sub(self, other: Self) -> Self {
        self + other.neg()
      }
    }

    impl SubAssign for $Point {
      fn sub_assign(&mut self, other: $Point) {
        *self = *self - other;
      }
    }

    impl Sub<&$Point> for $Point {
      type Output = $Point;
      fn sub(self, other: &$Point) -> $Point {
        self - *other
      }
    }

    impl SubAssign<&$Point> for $Point {
      fn sub_assign(&mut self, other: &$Point) {
        *self -= *other;
      }
    }

    impl Group for $Point {
      type Scalar = $Scalar;
      fn random(mut rng: impl RngCore) -> Self {
        loop {
          let mut bytes = $Field::random(&mut rng).to_repr();
          let mut_ref: &mut [u8] = bytes.as_mut();
          mut_ref[31] |= u8::try_from(rng.next_u32() % 2).unwrap() << 7;
          let opt = Self::from_bytes(&bytes);
          if opt.is_some().into() {
            return opt.unwrap();
          }
        }
      }
      fn identity() -> Self {
        $Point { x: $Field::ZERO, y: $Field::ONE, z: $Field::ONE }
      }
      fn generator() -> Self {
        G
      }
      fn is_identity(&self) -> Choice {
        self.x.ct_eq(&$Field::ZERO)
      }
      fn double(&self) -> Self {
        // dbl-2009-l
        let a = self.x.square();
        let b = self.y.square();
        let c = b.square();
        let d = ((self.x + b).square() - a - c).double();
        let e = a.double() + a;
        let f = e.square();
        let x3 = f - d.double();
        let y3 = (e * (d - x3)) - c.double().double().double();
        let z3 = (self.y * self.z).double();

        $Point { x: x3, y: y3, z: z3 }
      }
    }

    impl Sum<$Point> for $Point {
      fn sum<I: Iterator<Item = $Point>>(iter: I) -> $Point {
        let mut res = Self::identity();
        for i in iter {
          res += i;
        }
        res
      }
    }

    impl<'a> Sum<&'a $Point> for $Point {
      fn sum<I: Iterator<Item = &'a $Point>>(iter: I) -> $Point {
        $Point::sum(iter.cloned())
      }
    }

    impl Mul<$Scalar> for $Point {
      type Output = $Point;
      fn mul(self, mut other: $Scalar) -> $Point {
        // Precompute the optimal amount that's a multiple of 2
        let mut table = [$Point::identity(); 16];
        table[1] = self;
        for i in 2 .. 16 {
          table[i] = table[i - 1] + self;
        }

        let mut res = Self::identity();
        let mut bits = 0;
        for (i, mut bit) in other.to_le_bits().iter_mut().rev().enumerate() {
          bits <<= 1;
          let mut bit = u8_from_bool(bit.deref_mut());
          bits |= bit;
          bit.zeroize();

          if ((i + 1) % 4) == 0 {
            if i != 3 {
              for _ in 0 .. 4 {
                res = res.double();
              }
            }
            res += table[usize::from(bits)];
            bits = 0;
          }
        }
        other.zeroize();
        res
      }
    }

    impl MulAssign<$Scalar> for $Point {
      fn mul_assign(&mut self, other: $Scalar) {
        *self = *self * other;
      }
    }

    impl Mul<&$Scalar> for $Point {
      type Output = $Point;
      fn mul(self, other: &$Scalar) -> $Point {
        self * *other
      }
    }

    impl MulAssign<&$Scalar> for $Point {
      fn mul_assign(&mut self, other: &$Scalar) {
        *self *= *other;
      }
    }

    impl GroupEncoding for $Point {
      type Repr = <$Field as PrimeField>::Repr;

      fn from_bytes(bytes: &Self::Repr) -> CtOption<Self> {
        // Extract and clear the sign bit
        let sign = Choice::from(bytes[31] >> 7);
        let mut bytes = *bytes;
        let mut_ref: &mut [u8] = bytes.as_mut();
        mut_ref[31] &= !(1 << 7);

        // Parse x, recover y
        $Field::from_repr(bytes).and_then(|x| {
          let is_identity = x.is_zero();

          let y = recover_y(x).map(|mut y| {
            y.conditional_negate(y.is_odd().ct_eq(&!sign));
            y
          });

          // If this the identity, set y to 1
          let y =
            CtOption::conditional_select(&y, &CtOption::new($Field::ONE, 1.into()), is_identity);
          // Create the point if we have a y solution
          let point = y.map(|y| $Point { x, y, z: $Field::ONE });

          let not_negative_zero = !(is_identity & sign);
          // Only return the point if it isn't -0
          CtOption::conditional_select(
            &CtOption::new($Point::identity(), 0.into()),
            &point,
            not_negative_zero,
          )
        })
      }

      fn from_bytes_unchecked(bytes: &Self::Repr) -> CtOption<Self> {
        $Point::from_bytes(bytes)
      }

      fn to_bytes(&self) -> Self::Repr {
        let z = self.z.invert().unwrap();
        let z2 = z.square();
        let z3 = z2 * z;
        let x = self.x * z2;
        let y = self.y * z3;

        let mut bytes = x.to_repr();
        let mut_ref: &mut [u8] = bytes.as_mut();

        // Normalize the sign to 0 when x is 0
        let y_sign = u8::conditional_select(&y.is_odd().unwrap_u8(), &0, x.ct_eq(&$Field::ZERO));
        mut_ref[31] |= y_sign << 7;
        bytes
      }
    }

    impl PrimeGroup for $Point {}
  };
}

mod alpha {
  use super::*;
  curve!(
    SmallerElement,
    LargerElement,
    AlphaPoint,
    // printf "Tevone Generator" | sha256sum
    // TODO: Can we use the same generator, by X and Y coordinates, on both curves?
    "a9125a8fd2036e752fe1d9ce08f8bd620d49c62afaafdc8ee158976e3f70dc2d",
    "65e5e7b468f2c49ff94634832fa01e5df660aad2086485a4e0cc2a3c14de7c1d",
  );

  #[test]
  fn test_alpha() {
    ff_group_tests::group::test_prime_group_bits::<_, AlphaPoint>(&mut rand_core::OsRng);
  }

  #[test]
  fn generator_alpha() {
    use alpha::{G_X, G_Y, G};
    assert!(G.x == G_X);
    assert!(G.y == G_Y);
    assert!(recover_y(G.x).unwrap() == G.y);
  }
}
pub use alpha::AlphaPoint;

mod beta {
  use super::*;
  curve!(
    LargerElement,
    SmallerElement,
    BetaPoint,
    // printf "Tevone Generator" | sha256sum
    "a9125a8fd2036e752fe1d9ce08f8bd620d49c62afaafdc8ee158976e3f70dc2d",
    "38541b0fa996b498c6b8142302db5ca810c176a63ddbf610e1259050e493811b",
  );

  #[test]
  fn test_beta() {
    ff_group_tests::group::test_prime_group_bits::<_, BetaPoint>(&mut rand_core::OsRng);
  }

  #[test]
  fn generator_beta() {
    use beta::{G_X, G_Y, G};
    assert!(G.x == G_X);
    assert!(G.y == G_Y);
    assert!(recover_y(G.x).unwrap() == G.y);
  }
}
pub use beta::BetaPoint;

// Checks random won't infinitely loop
#[test]
fn random() {
  AlphaPoint::random(&mut rand_core::OsRng);
  BetaPoint::random(&mut rand_core::OsRng);
}
