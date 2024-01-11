#![allow(non_snake_case)]

use std::collections::{HashSet, HashMap};

use zeroize::{Zeroize, ZeroizeOnDrop};

use rand_core::{RngCore, CryptoRng};

use transcript::Transcript;
use multiexp::{multiexp_vartime, Point as MultiexpPoint};
use ciphersuite::{
  group::{ff::Field, Group, GroupEncoding},
  Ciphersuite,
};

mod scalar_vector;
pub use scalar_vector::ScalarVector;
mod scalar_matrix;
pub use scalar_matrix::ScalarMatrix;
mod point_vector;
pub use point_vector::PointVector;

pub mod inner_product;

pub(crate) mod arithmetic_circuit_proof;
pub mod arithmetic_circuit;
pub mod gadgets;

#[cfg(any(test, feature = "tests"))]
pub mod tests;

pub const RANGE_PROOF_BITS: usize = 64;

pub fn padded_pow_of_2(i: usize) -> usize {
  let mut next_pow_of_2 = 1;
  while next_pow_of_2 < i {
    next_pow_of_2 <<= 1;
  }
  next_pow_of_2
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub(crate) enum GeneratorsList {
  GBold1,
  HBold1,
}

// TODO: Should these all be static? Should MultiexpPoint itself work off &'static references?
// TODO: Table these
#[derive(Clone, Debug)]
pub struct Generators<T: 'static + Transcript, C: Ciphersuite> {
  g: MultiexpPoint<C::G>,
  h: MultiexpPoint<C::G>,

  g_bold1: Vec<MultiexpPoint<C::G>>,
  h_bold1: Vec<MultiexpPoint<C::G>>,

  transcript: T,
}

#[derive(Clone, Debug)]
pub struct ProofGenerators<'a, T: 'static + Transcript, C: Ciphersuite> {
  g: &'a MultiexpPoint<C::G>,
  h: &'a MultiexpPoint<C::G>,

  g_bold1: &'a [MultiexpPoint<C::G>],
  h_bold1: &'a [MultiexpPoint<C::G>],

  transcript: T,
}

#[derive(Clone, Debug)]
pub struct InnerProductGenerators<'a, T: 'static + Transcript, C: Ciphersuite> {
  g: &'a MultiexpPoint<C::G>,
  h: &'a MultiexpPoint<C::G>,

  g_bold1: &'a [MultiexpPoint<C::G>],
  h_bold1: &'a [MultiexpPoint<C::G>],

  transcript: T,
}

impl<T: 'static + Transcript, C: Ciphersuite> Generators<T, C> {
  pub fn new(g: C::G, h: C::G, mut g_bold1: Vec<C::G>, mut h_bold1: Vec<C::G>) -> Self {
    assert!(!g_bold1.is_empty());
    assert_eq!(g_bold1.len(), h_bold1.len());

    assert_eq!(padded_pow_of_2(g_bold1.len()), g_bold1.len(), "generators must be a pow of 2");

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
    for h in &h_bold1 {
      add_generator(b"h_bold1", h);
    }

    Generators {
      g: MultiexpPoint::new_constant(g),
      h: MultiexpPoint::new_constant(h),

      g_bold1: g_bold1.drain(..).map(MultiexpPoint::new_constant).collect(),
      h_bold1: h_bold1.drain(..).map(MultiexpPoint::new_constant).collect(),

      transcript,
    }
  }

  pub fn g(&self) -> &MultiexpPoint<C::G> {
    &self.g
  }

  pub fn h(&self) -> &MultiexpPoint<C::G> {
    &self.h
  }

  /// Take a presumably global Generators object and return a new object usable per-proof.
  ///
  /// Cloning Generators is expensive. This solely takes references to the generators.
  pub fn per_proof(&self) -> ProofGenerators<'_, T, C> {
    ProofGenerators {
      g: &self.g,
      h: &self.h,

      g_bold1: &self.g_bold1,
      h_bold1: &self.h_bold1,

      transcript: self.transcript.clone(),
    }
  }
}

impl<'a, T: 'static + Transcript, C: Ciphersuite> ProofGenerators<'a, T, C> {
  pub fn g(&self) -> &MultiexpPoint<C::G> {
    self.g
  }

  pub fn h(&self) -> &MultiexpPoint<C::G> {
    self.h
  }

  pub(crate) fn generator(&self, list: GeneratorsList, i: usize) -> &MultiexpPoint<C::G> {
    &(match list {
      GeneratorsList::GBold1 => &self.g_bold1,
      GeneratorsList::HBold1 => &self.h_bold1,
    })[i]
  }

  pub(crate) fn reduce(mut self, generators: usize) -> InnerProductGenerators<'a, T, C> {
    // Round to the nearest power of 2
    let generators = padded_pow_of_2(generators);
    assert!(generators <= self.g_bold1.len());

    self.g_bold1 = &self.g_bold1[.. generators];
    self.h_bold1 = &self.h_bold1[.. generators];
    self
      .transcript
      .append_message(b"used_generators", u32::try_from(generators).unwrap().to_le_bytes());

    InnerProductGenerators {
      g: self.g,
      h: self.h,

      g_bold1: self.g_bold1,
      h_bold1: self.h_bold1,

      // TODO: Can this be replaced with just a challenge?
      transcript: self.transcript.clone(),
    }
  }
}

impl<'a, T: 'static + Transcript, C: Ciphersuite> InnerProductGenerators<'a, T, C> {
  pub(crate) fn len(&self) -> usize {
    self.g_bold1.len()
  }

  pub(crate) fn g(&self) -> &MultiexpPoint<C::G> {
    self.g
  }

  pub(crate) fn h(&self) -> &MultiexpPoint<C::G> {
    self.h
  }

  // TODO: Replace with g_bold + h_bold
  pub(crate) fn generator(&self, mut list: GeneratorsList, mut i: usize) -> &MultiexpPoint<C::G> {
    &(match list {
      GeneratorsList::GBold1 => self.g_bold1.as_ref(),
      GeneratorsList::HBold1 => self.h_bold1,
    })[i]
  }
}
