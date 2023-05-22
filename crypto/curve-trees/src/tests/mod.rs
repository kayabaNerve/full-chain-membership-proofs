use pasta_curves::arithmetic::{Coordinates, CurveExt, CurveAffine};
use ciphersuite::{
  group::{ff::Field, Curve},
  Ciphersuite, Pallas, Vesta,
};

use crate::CurveCycle;

mod tree;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Pasta {}
impl CurveCycle for Pasta {
  type C1 = Pallas;
  type C2 = Vesta;

  fn c1_coords(
    point: <Self::C1 as Ciphersuite>::G,
  ) -> (<Self::C2 as Ciphersuite>::F, <Self::C2 as Ciphersuite>::F) {
    Option::<Coordinates<_>>::from(point.to_affine().coordinates())
      .map(|coords| (*coords.x(), *coords.y()))
      .unwrap_or((<Self::C2 as Ciphersuite>::F::ZERO, <Self::C2 as Ciphersuite>::F::ZERO))
  }
  fn c2_coords(
    point: <Self::C2 as Ciphersuite>::G,
  ) -> (<Self::C1 as Ciphersuite>::F, <Self::C1 as Ciphersuite>::F) {
    Option::<Coordinates<_>>::from(point.to_affine().coordinates())
      .map(|coords| (*coords.x(), *coords.y()))
      .unwrap_or((<Self::C1 as Ciphersuite>::F::ZERO, <Self::C1 as Ciphersuite>::F::ZERO))
  }

  fn c1_hash_to_curve(label: &'static str, value: &[u8]) -> <Self::C1 as Ciphersuite>::G {
    <Pallas as Ciphersuite>::G::hash_to_curve(label)(value)
  }
  fn c2_hash_to_curve(label: &'static str, value: &[u8]) -> <Self::C2 as Ciphersuite>::G {
    <Vesta as Ciphersuite>::G::hash_to_curve(label)(value)
  }
}
