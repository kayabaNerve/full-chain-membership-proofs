use zeroize::{DefaultIsZeroes, Zeroize};

use crypto_bigint::{
  U256, U512,
  modular::constant_mod::{ResidueParams, Residue},
};

const MODULUS_STR: &str = "68dbeec000000000000000000000000000000000000000000000000000000001";

impl_modulus!(FieldModulus, U256, MODULUS_STR);
type ResidueType = Residue<FieldModulus, { FieldModulus::LIMBS }>;

/// Smaller field element.
#[derive(Clone, Copy, PartialEq, Eq, Default, Debug)]
pub struct SmallerElement(pub(crate) ResidueType);

impl DefaultIsZeroes for SmallerElement {}

// (27488187 * (2 ** 230)) + 1
pub(crate) const MODULUS: U256 = U256::from_be_hex(MODULUS_STR);

const WIDE_MODULUS: U512 = U512::from_be_hex(concat!(
  "0000000000000000000000000000000000000000000000000000000000000000",
  "68dbeec000000000000000000000000000000000000000000000000000000001",
));

field!(
  SmallerElement,
  ResidueType,
  MODULUS_STR,
  MODULUS,
  WIDE_MODULUS,
  17,
  230,
  "205ed76511a82c3650d02679ef690c7ef86b75b36722442f8a12affbfbcddbed",
  "038c8f5ea209b954c6c176dde0adb7d4a96b6ed3d9100468ef497e6df00a6004",
  "0000000000000000000000000000000000000000000000000000000000d1b7dd",
);

impl SmallerElement {
  /// Perform a wide reduction to obtain a non-biased SmallerElement.
  pub fn wide_reduce(bytes: [u8; 64]) -> SmallerElement {
    SmallerElement(Residue::new(&reduce(U512::from_le_slice(bytes.as_ref()))))
  }
}

#[test]
fn test_smaller() {
  ff_group_tests::prime_field::test_prime_field_bits::<_, SmallerElement>(&mut rand_core::OsRng);
}
