use zeroize::{DefaultIsZeroes, Zeroize};

use crypto_bigint::{
  U256, U512,
  modular::constant_mod::{ResidueParams, Residue},
};

const MODULUS_STR: &str = "68dbeec00000000000000000000000011bc80000000000000000000000000001";

impl_modulus!(LargerModulus, U256, MODULUS_STR);
type ResidueType = Residue<LargerModulus, { LargerModulus::LIMBS }>;

/// Larger field element.
#[derive(Clone, Copy, PartialEq, Eq, Default, Debug)]
pub struct LargerElement(pub(crate) ResidueType);

impl DefaultIsZeroes for LargerElement {}

pub(crate) const MODULUS: U256 = U256::from_be_hex(MODULUS_STR);

const WIDE_MODULUS: U512 = U512::from_be_hex(concat!(
  "0000000000000000000000000000000000000000000000000000000000000000",
  "68dbeec00000000000000000000000011bc80000000000000000000000000001",
));

field!(
  LargerElement,
  ResidueType,
  MODULUS_STR,
  MODULUS,
  WIDE_MODULUS,
  11,
  115,
  "68630c7180e309ee3b81bdd35b965697dee2caa8fa2b1e845d3778e4e476b87a",
  "272e9d3a279f1e54abd06109b64c35f4f759ab7502ad5f2034df2f851db781a3",
  "0000000000000000000000000000068dbeec00000000000000000000000011bc",
);

impl LargerElement {
  /// Perform a wide reduction to obtain a non-biased LargerElement.
  pub fn wide_reduce(bytes: [u8; 64]) -> LargerElement {
    LargerElement(Residue::new(&reduce(U512::from_le_slice(bytes.as_ref()))))
  }
}

#[test]
fn test_larger() {
  ff_group_tests::prime_field::test_prime_field_bits::<_, LargerElement>(&mut rand_core::OsRng);
}
