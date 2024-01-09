#![allow(non_snake_case)]

use zeroize::{Zeroize, ZeroizeOnDrop};
use subtle::ConditionallySelectable;

use rand_core::{RngCore, CryptoRng};

use transcript::Transcript;

use crypto_bigint::{CheckedAdd, CheckedMul, Random, U256};
use ciphersuite::{
  group::{
    ff::{Field, PrimeField},
    GroupEncoding,
  },
  Ciphersuite,
};

use bulletproofs_plus::RangeCommitment;

#[cfg(test)]
mod tests;

const BX: u32 = 64; // 64-bit value
const BC: u32 = 128; // 128-bit security

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Statement<C1: Ciphersuite, C2: Ciphersuite> {
  g1: C1::G,
  h1: C1::G,
  g2: C2::G,
  h2: C2::G,
  commitment_1: C1::G,
  commitment_2: C2::G,
}

#[derive(Clone, PartialEq, Eq, Debug, Zeroize, ZeroizeOnDrop)]
pub struct Witness<C1: Ciphersuite, C2: Ciphersuite> {
  commitment_1: RangeCommitment<C1>,
  commitment_2: RangeCommitment<C2>,
}

impl<C1: Ciphersuite, C2: Ciphersuite> Witness<C1, C2> {
  pub fn new(commitment_1: RangeCommitment<C1>, commitment_2: RangeCommitment<C2>) -> Self {
    Self { commitment_1, commitment_2 }
  }
}

#[derive(Clone, PartialEq, Eq, Debug, Zeroize)]
pub struct Proof<C1: Ciphersuite, C2: Ciphersuite> {
  K1: C1::G,
  K2: C2::G,
  z: U256,
  s1: C1::F,
  s2: C2::F,
}

fn scalar_from_u256<C: Ciphersuite>(value: &U256) -> C::F {
  let mut bit = C::F::ONE;
  let mut res = C::F::ZERO;
  for i in 0 .. 256 {
    res = C::F::conditional_select(&res, &(res + bit), value.bit(i).into());
    bit = bit.double();
  }
  res
}

fn z_in_range(z: &U256, bf: u32) -> bool {
  let bit_sum = usize::try_from(BX + BC + bf).unwrap();
  debug_assert!(bit_sum <= 255);

  if z.rem2k(bit_sum) != *z {
    return false;
  }
  if z < &(U256::ONE << usize::try_from(BX + BC).unwrap()) {
    return false;
  }
  true
}

impl<C1: Ciphersuite, C2: Ciphersuite> Statement<C1, C2> {
  pub fn new(
    g1: C1::G,
    h1: C1::G,
    g2: C2::G,
    h2: C2::G,
    commitment_1: C1::G,
    commitment_2: C2::G,
  ) -> Self {
    Self { g1, h1, g2, h2, commitment_1, commitment_2 }
  }

  fn bf() -> u32 {
    let capacity = C1::F::CAPACITY.min(C2::F::CAPACITY);
    // The failure rate is 1 / bf
    let bf = (capacity.saturating_sub(BC).saturating_sub(BX)).min(63);
    assert!(bf > 1);
    bf
  }

  fn initial_transcript<T: Transcript>(&self, transcript: &mut T) {
    transcript.domain_separate(b"COPZ-DLEq");
    transcript.append_message(b"G1", self.g1.to_bytes());
    transcript.append_message(b"H1", self.h1.to_bytes());
    transcript.append_message(b"G2", self.g2.to_bytes());
    transcript.append_message(b"H2", self.h2.to_bytes());
    transcript.append_message(b"C1", self.commitment_1.to_bytes());
    transcript.append_message(b"C2", self.commitment_2.to_bytes());
  }

  fn challenge<T: Transcript>(transcript: &mut T, K1: C1::G, K2: C2::G) -> U256 {
    transcript.append_message(b"K1", K1.to_bytes());
    transcript.append_message(b"K2", K2.to_bytes());
    U256::from_le_slice(&transcript.challenge(b"c").as_ref()[.. 32])
      .rem2k(usize::try_from(BC).unwrap())
  }

  pub fn prove<R: RngCore + CryptoRng, T: Transcript>(
    self,
    rng: &mut R,
    transcript_var: &mut T,
    witness: Witness<C1, C2>,
  ) -> Proof<C1, C2> {
    assert_eq!(witness.commitment_1.calculate(self.g1, self.h1), self.commitment_1);
    assert_eq!(witness.commitment_2.calculate(self.g2, self.h2), self.commitment_2);
    assert_eq!(witness.commitment_1.value, witness.commitment_2.value);

    let bf = Self::bf();
    let bit_sum = usize::try_from(BX + BC + bf).unwrap();
    debug_assert!(bit_sum <= 255);

    self.initial_transcript(transcript_var);

    loop {
      let k = U256::random(&mut *rng).rem2k(bit_sum);

      let t1 = C1::F::random(&mut *rng);
      let t2 = C2::F::random(&mut *rng);

      let K1 = (self.g1 * scalar_from_u256::<C1>(&k)) + (self.h1 * t1);
      let K2 = (self.g2 * scalar_from_u256::<C2>(&k)) + (self.h2 * t2);

      let mut transcript = transcript_var.clone();

      let c = Self::challenge(&mut transcript, K1, K2);
      let Some(cx) = Option::from(c.checked_mul(&U256::from(witness.commitment_1.value))) else {
        continue;
      };
      let Some(z) = Option::from(k.checked_add(&cx)) else { continue };
      if !z_in_range(&z, bf) {
        continue;
      }
      let s1 = t1 + (scalar_from_u256::<C1>(&c) * witness.commitment_1.mask);
      let s2 = t2 + (scalar_from_u256::<C2>(&c) * witness.commitment_2.mask);

      *transcript_var = transcript;
      return Proof { K1, K2, z, s1, s2 };
    }
  }

  // TODO: Support batch verification
  pub fn verify<T: Transcript>(self, transcript: &mut T, proof: Proof<C1, C2>) {
    self.initial_transcript(transcript);

    let bf = Self::bf();
    assert!(z_in_range(&proof.z, bf));

    let c = Self::challenge(transcript, proof.K1, proof.K2);

    assert_eq!(
      (self.g1 * scalar_from_u256::<C1>(&proof.z)) + (self.h1 * proof.s1),
      (proof.K1 + (self.commitment_1 * scalar_from_u256::<C1>(&c))),
    );
    assert_eq!(
      (self.g2 * scalar_from_u256::<C2>(&proof.z)) + (self.h2 * proof.s2),
      (proof.K2 + (self.commitment_2 * scalar_from_u256::<C2>(&c))),
    );
  }
}
