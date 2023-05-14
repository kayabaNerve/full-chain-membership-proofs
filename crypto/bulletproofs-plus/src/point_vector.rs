use core::ops::{Index, IndexMut};

use zeroize::{Zeroize, ZeroizeOnDrop};

use ciphersuite::{group::Group, Ciphersuite};

use crate::ScalarVector;

#[derive(Clone, PartialEq, Eq, Debug, Zeroize, ZeroizeOnDrop)]
pub struct PointVector<C: Ciphersuite>(pub(crate) Vec<C::G>);

impl<C: Ciphersuite> Index<usize> for PointVector<C> {
  type Output = C::G;
  fn index(&self, index: usize) -> &C::G {
    &self.0[index]
  }
}

impl<C: Ciphersuite> IndexMut<usize> for PointVector<C> {
  fn index_mut(&mut self, index: usize) -> &mut C::G {
    &mut self.0[index]
  }
}

impl<C: Ciphersuite> PointVector<C> {
  pub(crate) fn new(len: usize) -> Self {
    PointVector(vec![C::G::identity(); len])
  }

  pub(crate) fn add(&self, point: impl AsRef<C::G>) -> Self {
    let mut res = self.clone();
    for val in res.0.iter_mut() {
      *val += point.as_ref();
    }
    res
  }
  pub(crate) fn sub(&self, point: impl AsRef<C::G>) -> Self {
    let mut res = self.clone();
    for val in res.0.iter_mut() {
      *val -= point.as_ref();
    }
    res
  }
  pub(crate) fn mul(&self, scalar: impl core::borrow::Borrow<C::F>) -> Self {
    let mut res = self.clone();
    for val in res.0.iter_mut() {
      *val *= scalar.borrow();
    }
    res
  }

  pub(crate) fn add_vec(&self, vector: &Self) -> Self {
    let mut res = self.clone();
    for (i, val) in res.0.iter_mut().enumerate() {
      *val += vector.0[i];
    }
    res
  }
  pub(crate) fn sub_vec(&self, vector: &Self) -> Self {
    let mut res = self.clone();
    for (i, val) in res.0.iter_mut().enumerate() {
      *val -= vector.0[i];
    }
    res
  }
  pub(crate) fn mul_vec(&self, vector: &ScalarVector<C>) -> Self {
    let mut res = self.clone();
    for (i, val) in res.0.iter_mut().enumerate() {
      *val *= vector.0[i];
    }
    res
  }

  pub(crate) fn sum(&self) -> C::G {
    self.0.iter().sum()
  }

  pub(crate) fn len(&self) -> usize {
    self.0.len()
  }

  pub(crate) fn split(mut self) -> (Self, Self) {
    assert!(self.len() > 1);
    assert_eq!(self.len() % 2, 0);
    let r = self.0.split_off(self.0.len() / 2);
    (self, PointVector(r))
  }
}
