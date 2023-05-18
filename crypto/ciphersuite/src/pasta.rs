use zeroize::Zeroize;

use blake2::{Digest, Blake2b512};

use group::{ff::FromUniformBytes, Group};

use crate::Ciphersuite;

macro_rules! pasta_curve {
  (
    $lib:     ident,

    $Ciphersuite: ident,
    $ID:          literal
  ) => {
    impl Ciphersuite for $Ciphersuite {
      type F = pasta_curves::$lib::Scalar;
      type G = pasta_curves::$lib::Point;
      type H = Blake2b512;

      const ID: &'static [u8] = $ID;

      fn generator() -> Self::G {
        pasta_curves::$lib::Point::generator()
      }

      fn hash_to_F(dst: &[u8], msg: &[u8]) -> Self::F {
        let mut uniform = [0; 64];
        let mut hash = Blake2b512::digest(&[dst, msg].concat());
        uniform.copy_from_slice(hash.as_ref());
        let hash_as_mut: &mut [u8] = hash.as_mut();
        hash_as_mut.zeroize();
        let res = pasta_curves::$lib::Scalar::from_uniform_bytes(&uniform);
        uniform.zeroize();
        res
      }
    }
  };
}

/// Ciphersuite for Pallas.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Zeroize)]
pub struct Pallas;
pasta_curve!(pallas, Pallas, b"Pallas");

/// Ciphersuite for Vesta.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Zeroize)]
pub struct Vesta;
pasta_curve!(vesta, Vesta, b"Vesta");
