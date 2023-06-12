#![allow(non_snake_case)]

use std::collections::HashSet;

use zeroize::{Zeroize, ZeroizeOnDrop};

use rand_core::{RngCore, CryptoRng};

use transcript::Transcript;
use multiexp::{Point as MultiexpPoint};
use ciphersuite::{
  group::{ff::Field, Group, GroupEncoding},
  Ciphersuite,
};

mod scalar_vector;
pub use scalar_vector::{ScalarVector, weighted_inner_product};
mod scalar_matrix;
pub use scalar_matrix::ScalarMatrix;
mod point_vector;
pub use point_vector::PointVector;

pub mod weighted_inner_product;
pub mod single_range_proof;
pub mod aggregate_range_proof;

pub(crate) mod arithmetic_circuit_proof;
pub mod arithmetic_circuit;
pub mod gadgets;

#[cfg(any(test, feature = "tests"))]
pub mod tests;

pub const RANGE_PROOF_BITS: usize = 64;

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub(crate) enum GeneratorsList {
  GBold1,
  GBold2,
  HBold1,
}

// TODO: Table these
#[derive(Clone, Debug)]
pub struct Generators<T: Transcript, C: Ciphersuite> {
  pub(crate) g: MultiexpPoint<C::G>,
  pub(crate) h: MultiexpPoint<C::G>,
  pub(crate) g_bold1: Vec<MultiexpPoint<C::G>>,
  pub(crate) g_bold2: Vec<MultiexpPoint<C::G>>,
  h_bold1: Vec<MultiexpPoint<C::G>>,
  h_bold2: Vec<MultiexpPoint<C::G>>,

  proving_gs: Option<(MultiexpPoint<C::G>, MultiexpPoint<C::G>)>,
  proving_h_bolds: Option<(Vec<MultiexpPoint<C::G>>, Vec<MultiexpPoint<C::G>>)>,

  // Uses a Vec<u8> since C::G doesn't impl Hash
  set: HashSet<Vec<u8>>,
  transcript: T,
}
impl<T: Transcript, C: Ciphersuite> Zeroize for Generators<T, C> {
  fn zeroize(&mut self) {
    self.g.zeroize();
    self.h.zeroize();
    self.g_bold1.zeroize();
    self.g_bold2.zeroize();
    self.h_bold1.zeroize();
    self.h_bold2.zeroize();

    self.proving_gs.zeroize();
    self.proving_h_bolds.zeroize();

    // Since we don't zeroize set, this is of arguable practicality
  }
}

type MultiexpDecompose<C> = (
  MultiexpPoint<<C as Ciphersuite>::G>,
  MultiexpPoint<<C as Ciphersuite>::G>,
  Vec<MultiexpPoint<<C as Ciphersuite>::G>>,
  Vec<MultiexpPoint<<C as Ciphersuite>::G>>,
);

// TODO: This is a monolithic type which makes a ton of assumptions about its usage flow
// It needs to be split into distinct types which clearly documented valid use cases
impl<T: Transcript, C: Ciphersuite> Generators<T, C> {
  pub fn new(
    g: C::G,
    h: C::G,
    mut g_bold1: Vec<C::G>,
    mut g_bold2: Vec<C::G>,
    mut h_bold1: Vec<C::G>,
    mut h_bold2: Vec<C::G>,
  ) -> Self {
    assert!(!g_bold1.is_empty());
    assert_eq!(g_bold1.len(), g_bold2.len());
    assert_eq!(h_bold1.len(), h_bold2.len());
    assert_eq!(g_bold1.len(), h_bold1.len());

    let mut transcript = T::new(b"Bulletproofs+ Generators");

    transcript.domain_separate(b"generators");
    let mut set = HashSet::new();
    let mut add_generator = |label, generator: &C::G| {
      assert!(!bool::from(generator.is_identity()));
      let bytes = generator.to_bytes();
      transcript.append_message(label, bytes);
      assert!(set.insert(bytes.as_ref().to_vec()));
    };

    add_generator(b"g", &g);
    add_generator(b"h", &h);
    for g in &g_bold1 {
      add_generator(b"g_bold1", g);
    }
    for g in &g_bold2 {
      add_generator(b"g_bold2", g);
    }
    for h in &h_bold1 {
      add_generator(b"h_bold1", h);
    }
    for h in &h_bold2 {
      add_generator(b"h_bold2", h);
    }

    Generators {
      g: MultiexpPoint::Constant(g.to_bytes().as_ref().to_vec(), g),
      h: MultiexpPoint::Constant(h.to_bytes().as_ref().to_vec(), h),
      g_bold1: g_bold1
        .drain(..)
        .map(|point| MultiexpPoint::Constant(point.to_bytes().as_ref().to_vec(), point))
        .collect(),
      g_bold2: g_bold2
        .drain(..)
        .map(|point| MultiexpPoint::Constant(point.to_bytes().as_ref().to_vec(), point))
        .collect(),
      h_bold1: h_bold1
        .drain(..)
        .map(|point| MultiexpPoint::Constant(point.to_bytes().as_ref().to_vec(), point))
        .collect(),
      h_bold2: h_bold2
        .drain(..)
        .map(|point| MultiexpPoint::Constant(point.to_bytes().as_ref().to_vec(), point))
        .collect(),

      proving_gs: None,
      proving_h_bolds: None,

      set,
      transcript,
    }
  }

  // Add generators used for proving the vector commitments validity
  pub fn add_vector_commitment_proving_generators(
    &mut self,
    gs: (C::G, C::G),
    mut h_bold1: (Vec<C::G>, Vec<C::G>),
  ) {
    self.transcript.domain_separate(b"vector_commitment_proving_generators");

    let mut add_generator = |label, generator: &C::G| {
      assert!(!bool::from(generator.is_identity()));
      let bytes = generator.to_bytes();
      self.transcript.append_message(label, bytes.as_ref());
      assert!(self.set.insert(bytes.as_ref().to_vec()));
    };

    add_generator(b"g0", &gs.0);
    add_generator(b"g1", &gs.1);

    for h_bold in &h_bold1.0 {
      add_generator(b"h_bold0", h_bold);
    }
    for h_bold in &h_bold1.1 {
      add_generator(b"h_bold1", h_bold);
    }

    self.proving_gs = Some((
      MultiexpPoint::Constant(gs.0.to_bytes().as_ref().to_vec(), gs.0),
      MultiexpPoint::Constant(gs.1.to_bytes().as_ref().to_vec(), gs.1),
    ));
    self.proving_h_bolds = Some((
      h_bold1
        .0
        .drain(..)
        .map(|point| MultiexpPoint::Constant(point.to_bytes().as_ref().to_vec(), point))
        .collect(),
      h_bold1
        .1
        .drain(..)
        .map(|point| MultiexpPoint::Constant(point.to_bytes().as_ref().to_vec(), point))
        .collect(),
    ));
  }

  fn vector_commitment_generators(
    &self,
    vc_generators: Vec<(GeneratorsList, usize)>,
  ) -> (Self, Self) {
    let gs = self.proving_gs.clone().unwrap();
    let (h_bold0, h_bold1) = self.proving_h_bolds.clone().unwrap();

    let mut g_bold1 = vec![];
    let mut transcript = self.transcript.clone();
    transcript.domain_separate(b"vector_commitment_proving_generators");
    for (list, i) in vc_generators {
      transcript.append_message(
        b"list",
        match list {
          GeneratorsList::GBold1 => {
            g_bold1.push(self.g_bold1[i].clone());
            b"g_bold1"
          }
          GeneratorsList::HBold1 => {
            g_bold1.push(self.h_bold1[i].clone());
            b"h_bold1"
          }
          GeneratorsList::GBold2 => {
            g_bold1.push(self.g_bold2[i].clone());
            b"g_bold2"
          }
        },
      );
      transcript
        .append_message(b"vector_commitment_generator", u32::try_from(i).unwrap().to_le_bytes());
    }

    let mut generators_0 = Generators {
      g: gs.0,
      h: self.h.clone(),
      g_bold1: g_bold1.clone(),
      g_bold2: vec![],
      h_bold1: h_bold0,
      h_bold2: vec![],
      proving_gs: None,
      proving_h_bolds: None,
      set: self.set.clone(),
      transcript: transcript.clone(),
    };
    generators_0.transcript.append_message(b"generators", "0");

    let mut generators_1 = Generators {
      g: gs.1,
      h: self.h.clone(),
      g_bold1,
      g_bold2: vec![],
      h_bold1,
      h_bold2: vec![],
      proving_gs: None,
      proving_h_bolds: None,
      set: self.set.clone(),
      transcript,
    };
    generators_1.transcript.append_message(b"generators", "1");

    (generators_0, generators_1)
  }

  pub(crate) fn insert_generator(&mut self, gen: (GeneratorsList, usize), generator: C::G) {
    // Make sure this hasn't been used yet
    assert!(!self.g_bold2.is_empty());

    let (list, index) = gen;

    assert!(!bool::from(generator.is_identity()));

    let bytes = generator.to_bytes();
    self.transcript.domain_separate(b"inserted_generator");
    self.transcript.append_message(
      b"list",
      match list {
        GeneratorsList::GBold1 => b"g_bold1",
        GeneratorsList::GBold2 => b"g_bold2",
        GeneratorsList::HBold1 => b"h_bold1",
      },
    );
    self.transcript.append_message(b"index", u32::try_from(index).unwrap().to_le_bytes());
    self.transcript.append_message(b"generator", bytes);

    assert!(self.set.insert(bytes.as_ref().to_vec()));

    // TODO: Take in a MultiexpPoint
    (match list {
      GeneratorsList::GBold1 => &mut self.g_bold1,
      GeneratorsList::GBold2 => &mut self.g_bold2,
      GeneratorsList::HBold1 => &mut self.h_bold1,
    })[index] = MultiexpPoint::Constant(generator.to_bytes().as_ref().to_vec(), generator);
  }

  pub(crate) fn truncate(&mut self, generators: usize) {
    self.g_bold1.truncate(generators);
    self.g_bold2.truncate(generators);
    self.h_bold1.truncate(generators);
    self.h_bold2.truncate(generators);
    self
      .transcript
      .append_message(b"used_generators", u32::try_from(generators).unwrap().to_le_bytes());
  }

  pub fn reduce(mut self, generators: usize, with_secondaries: bool) -> Self {
    self.truncate(generators);
    if with_secondaries {
      self.transcript.append_message(b"secondaries", b"true");
      self.g_bold1.append(&mut self.g_bold2);
      self.h_bold1.append(&mut self.h_bold2);
    } else {
      self.transcript.append_message(b"secondaries", b"false");
      self.g_bold2.clear();
      self.h_bold2.clear();
    }
    self
  }

  pub(crate) fn g(&self) -> C::G {
    let MultiexpPoint::Constant(_, g) = self.g.clone() else { unreachable!() };
    g
  }

  pub fn h(&self) -> C::G {
    let MultiexpPoint::Constant(_, h) = self.h.clone() else { unreachable!() };
    h
  }

  pub(crate) fn g_bold(&self) -> PointVector<C> {
    PointVector(
      self
        .g_bold1
        .iter()
        .map(|point| {
          let MultiexpPoint::Constant(_, g) = point.clone() else { unreachable!() };
          g
        })
        .collect::<Vec<_>>(),
    )
  }

  pub(crate) fn h_bold(&self) -> PointVector<C> {
    PointVector(
      self
        .h_bold1
        .iter()
        .map(|point| {
          let MultiexpPoint::Constant(_, g) = point.clone() else { unreachable!() };
          g
        })
        .collect::<Vec<_>>(),
    )
  }

  pub(crate) fn g_bold2(&self) -> PointVector<C> {
    PointVector(
      self
        .g_bold2
        .iter()
        .map(|point| {
          let MultiexpPoint::Constant(_, g) = point.clone() else { unreachable!() };
          g
        })
        .collect::<Vec<_>>(),
    )
  }

  pub(crate) fn h_bold2(&self) -> PointVector<C> {
    PointVector(
      self
        .h_bold2
        .iter()
        .map(|point| {
          let MultiexpPoint::Constant(_, g) = point.clone() else { unreachable!() };
          g
        })
        .collect::<Vec<_>>(),
    )
  }

  pub(crate) fn multiexp_g(&self) -> MultiexpPoint<C::G> {
    self.g.clone()
  }

  pub(crate) fn multiexp_h(&self) -> MultiexpPoint<C::G> {
    self.h.clone()
  }

  pub(crate) fn multiexp_g_bold(&self) -> &[MultiexpPoint<C::G>] {
    &self.g_bold1
  }

  pub(crate) fn multiexp_h_bold(&self) -> &[MultiexpPoint<C::G>] {
    &self.h_bold1
  }

  pub(crate) fn multiexp_g_bold2(&self) -> &[MultiexpPoint<C::G>] {
    &self.g_bold2
  }

  pub(crate) fn multiexp_h_bold2(&self) -> &[MultiexpPoint<C::G>] {
    &self.h_bold2
  }

  pub fn decompose(self) -> (C::G, C::G, PointVector<C>, PointVector<C>) {
    assert!(self.g_bold2.is_empty());
    (self.g(), self.h(), self.g_bold(), self.h_bold())
  }

  pub fn multiexp_decompose(self) -> MultiexpDecompose<C> {
    assert!(self.g_bold2.is_empty());
    (self.g, self.h, self.g_bold1, self.h_bold1)
  }
}

#[allow(non_snake_case)]
#[derive(Clone, PartialEq, Eq, Debug, Zeroize, ZeroizeOnDrop)]
pub struct RangeCommitment<C: Ciphersuite> {
  pub value: u64,
  pub mask: C::F,
}

impl<C: Ciphersuite> RangeCommitment<C> {
  pub fn zero() -> Self {
    RangeCommitment { value: 0, mask: C::F::ZERO }
  }

  pub fn new(value: u64, mask: C::F) -> Self {
    RangeCommitment { value, mask }
  }

  pub fn masking<R: RngCore + CryptoRng>(rng: &mut R, value: u64) -> Self {
    RangeCommitment { value, mask: C::F::random(rng) }
  }

  /// Calculate a Pedersen commitment, as a point, from the transparent structure.
  pub fn calculate(&self, g: C::G, h: C::G) -> C::G {
    (g * C::F::from(self.value)) + (h * self.mask)
  }
}

// Returns the little-endian decomposition.
fn u64_decompose<C: Ciphersuite>(value: u64) -> ScalarVector<C> {
  let mut bits = ScalarVector::<C>::new(64);
  for bit in 0 .. 64 {
    bits[bit] = C::F::from((value >> bit) & 1);
  }
  bits
}
