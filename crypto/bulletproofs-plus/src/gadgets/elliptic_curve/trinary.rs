use subtle::{Choice, ConditionallySelectable};

use crypto_bigint::CheckedAdd;
use ciphersuite::{
  group::ff::{Field, PrimeFieldBits},
  UInt, Ciphersuite,
};

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Trit {
  NegOne,
  Zero,
  One,
}

pub fn trits_to_scalar<C: Ciphersuite>(trits: &[Trit]) -> C::F {
  let mut res = C::F::ZERO;
  let mut base = C::F::ONE;
  for trit in trits {
    // TODO: Make const time
    res += match trit {
      Trit::NegOne => -base,
      Trit::Zero => C::F::ZERO,
      Trit::One => base,
    };
    base *= C::F::from(3);
  }
  res
}

// TODO: This is not const time
pub fn scalar_to_trits<C: Ciphersuite>(scalar: C::F) -> Vec<Trit> {
  let mut uint = C::FI::ZERO;
  {
    let mut base = C::FI::ONE;
    let bits = scalar.to_le_bits();
    for (i, bit) in bits.iter().enumerate() {
      uint = uint
        .checked_add(&C::FI::conditional_select(&C::FI::ZERO, &base, Choice::from(u8::from(*bit))))
        .unwrap();
      if i != (bits.len() - 1) {
        base = base.checked_add(&base).unwrap();
      }
    }
  }

  let mut carry = false;
  let mut res = vec![];
  while uint != C::FI::ZERO {
    let rem;
    // TODO: Use an optimized division statement. This is using a 256-bit divisor for a 2-bit value
    (uint, rem) = uint.div_rem(C::FI::from(3));

    let new_carry;
    res.push(if rem == C::FI::ZERO {
      // Handle carry
      new_carry = false;
      if carry {
        Trit::One
      } else {
        Trit::Zero
      }
    } else if rem == C::FI::ONE {
      // Propagate carry
      new_carry = carry;
      if carry {
        Trit::NegOne
      } else {
        Trit::One
      }
    } else {
      // Set carry
      new_carry = true;
      if carry {
        Trit::Zero
      } else {
        Trit::NegOne
      }
    });
    carry = new_carry;
  }
  if carry {
    res.push(Trit::One);
  }

  debug_assert_eq!(scalar, trits_to_scalar::<C>(&res));
  res
}
