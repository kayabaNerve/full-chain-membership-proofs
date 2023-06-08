use rand_core::OsRng;

use ciphersuite::{
  group::{ff::Field, Group},
  Ciphersuite, Pallas,
};

use ecip::Ecip;

use crate::permissible::Permissible;

#[test]
fn test_permissible() {
  let permissible = Permissible::<Pallas> {
    h: <Pallas as Ciphersuite>::G::random(&mut OsRng),
    alpha: <Pallas as Ecip>::FieldElement::random(&mut OsRng),
    beta: <Pallas as Ecip>::FieldElement::random(&mut OsRng),
  };

  let runs = 1000;
  for _ in 0 .. runs {
    let point = permissible.make_permissible(<Pallas as Ciphersuite>::G::random(&mut OsRng)).1;
    assert!(permissible.elem(Pallas::to_xy(point).1));
    assert!(!permissible.elem(Pallas::to_xy(-point).1));
  }
}
