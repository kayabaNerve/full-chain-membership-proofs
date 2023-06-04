#![allow(non_snake_case)]

use core::marker::PhantomData;

use subtle::{ConditionallySelectable, Choice};
use rand_core::{RngCore, CryptoRng};

use ciphersuite::{
  group::ff::{Field, PrimeField, PrimeFieldBits},
  Ciphersuite,
};

use ecip::Ecip;
use bulletproofs_plus::{
  arithmetic_circuit::*,
  gadgets::{Bit, elliptic_curve::EmbeddedCurveOperations},
};

pub mod pedersen_hash;
pub mod tree;
use tree::*;

pub(crate) mod gadgets;
use gadgets::find_index_gadget;

#[cfg(test)]
pub mod tests;

pub trait CurveCycle: Clone + Copy + PartialEq + Eq + core::fmt::Debug {
  type C1: Ecip + EmbeddedCurveOperations<Embedded = Self::C2>;
  type C2: Ecip + EmbeddedCurveOperations<Embedded = Self::C1>;

  fn c1_coords(
    point: <Self::C1 as Ciphersuite>::G,
  ) -> (<Self::C2 as Ciphersuite>::F, <Self::C2 as Ciphersuite>::F);
  fn c2_coords(
    point: <Self::C2 as Ciphersuite>::G,
  ) -> (<Self::C1 as Ciphersuite>::F, <Self::C1 as Ciphersuite>::F);
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct FlipCurveCycle<C: CurveCycle>(PhantomData<C>);
impl<C: CurveCycle> CurveCycle for FlipCurveCycle<C> {
  type C1 = C::C2;
  type C2 = C::C1;

  fn c1_coords(
    point: <Self::C1 as Ciphersuite>::G,
  ) -> (<Self::C2 as Ciphersuite>::F, <Self::C2 as Ciphersuite>::F) {
    C::c2_coords(point)
  }
  fn c2_coords(
    point: <Self::C2 as Ciphersuite>::G,
  ) -> (<Self::C1 as Ciphersuite>::F, <Self::C1 as Ciphersuite>::F) {
    C::c1_coords(point)
  }
}

pub fn new_blind<R: RngCore + CryptoRng, C1: Ciphersuite, C2: Ciphersuite>(
  rng: &mut R,
) -> (C1::F, C2::F) {
  let capacity = C1::F::CAPACITY.min(C2::F::CAPACITY);
  let mut res = C1::F::ZERO;
  let mut pow = C1::F::ONE;
  // Only generate bits up to the mutual capacity
  for _ in 0 .. capacity {
    res += C1::F::conditional_select(
      &C1::F::ZERO,
      &pow,
      u8::try_from(rng.next_u64() % 2).unwrap().into(),
    );
    pow = pow.double();
  }

  // TODO: Support divisors when we have an odd amount of points and remove this
  if (res.to_le_bits().iter().filter(|bit| **bit).count() % 2) != 1 {
    return new_blind::<_, C1, C2>(rng);
  }

  let mut c2_repr = <C2::F as PrimeField>::Repr::default();
  c2_repr.as_mut().copy_from_slice(res.to_repr().as_ref());
  (res, C2::F::from_repr(c2_repr).unwrap())
}

pub fn layer_gadget<R: RngCore + CryptoRng, C: CurveCycle>(
  rng: &mut R,
  circuit: &mut Circuit<C::C2>,
  H: <C::C1 as Ciphersuite>::G,
  pedersen_generators: &[<C::C2 as Ciphersuite>::G],
  blinded_point: <C::C1 as Ciphersuite>::G,
  blind: Option<<C::C2 as Ciphersuite>::F>,
  elements: Vec<(Option<<C::C2 as Ciphersuite>::F>, Option<<C::C2 as Ciphersuite>::F>)>,
  last: bool,
) -> (Option<<C::C1 as Ciphersuite>::F>, <C::C2 as Ciphersuite>::G) {
  // Unblind the point
  let unblinded = {
    let (blind_x, blind_y) = if let Some(blind) = blind {
      let mut repr = <<C::C1 as Ciphersuite>::F as PrimeField>::Repr::default();
      repr.as_mut().copy_from_slice(blind.to_repr().as_ref());

      let coords = C::c1_coords(H * <C::C1 as Ciphersuite>::F::from_repr(repr).unwrap());
      (Some(coords.0), Some(coords.1))
    } else {
      (None, None)
    };
    let blind_x = circuit.add_secret_input(blind_x);
    let blind_y = circuit.add_secret_input(blind_y);
    let blind_var = C::C2::constrain_on_curve(circuit, blind_x, blind_y);

    // Prove we know the DLog of the point we're unblinding by to prevent unblinding by arbitrary
    // points
    {
      let capacity = usize::try_from(
        <C::C1 as Ciphersuite>::F::CAPACITY.min(<C::C2 as Ciphersuite>::F::CAPACITY),
      )
      .unwrap();
      let raw_bits = if let Some(blind) = blind {
        let mut bits = blind
          .to_le_bits()
          .iter()
          .map(|bit| Some(Choice::from(u8::try_from(*bit).unwrap())))
          .collect::<Vec<_>>();
        bits.truncate(capacity);
        bits
      } else {
        vec![None; capacity]
      };

      let mut dlog = vec![];
      for bit in raw_bits {
        dlog.push(Bit::new_from_choice(circuit, bit));
      }
      C::C2::dlog_pok(&mut *rng, circuit, H, blind_var, &dlog);
    }

    // Perform the addition
    let (point_x, point_y) = C::c1_coords(blinded_point);

    // The prover can set these variables to anything
    // TODO: Add incomplete_add where one point isn't ZK
    let point_x_var = circuit.add_secret_input(Some(point_x).filter(|_| circuit.prover()));
    let point_y_var = circuit.add_secret_input(Some(point_y).filter(|_| circuit.prover()));
    let point_var = C::C2::constrain_on_curve(circuit, point_x_var, point_y_var);
    // Constrain the above variables
    circuit.equals_constant(circuit.variable_to_product(point_x_var).unwrap(), point_x);
    circuit.equals_constant(circuit.variable_to_product(point_y_var).unwrap(), point_y);

    C::C2::incomplete_add(circuit, point_var, blind_var)
  };

  // Create the branch hash
  // TODO: Use a single-coord hash, as detailed in the Curve Trees paper
  {
    // Add the elements in this hash
    let mut x_coords = vec![];
    let mut y_coords = vec![];
    for elem in &elements {
      x_coords.push(circuit.add_secret_input(elem.0));
      y_coords.push(circuit.add_secret_input(elem.1));
      // TODO: This should be removable with architectural improvements
      circuit.product(*x_coords.last().unwrap(), *y_coords.last().unwrap());
    }

    // Ensure the unblnded point's x/y coordinates are actually present
    let x_pos = find_index_gadget(circuit, unblinded.x(), &x_coords);
    let x_pos = circuit.variable_to_product(x_pos).unwrap();
    let y_pos = find_index_gadget(circuit, unblinded.y(), &y_coords);
    let y_pos = circuit.variable_to_product(y_pos).unwrap();
    circuit.constrain_equality(x_pos, y_pos);

    // Bind these to the branch hash
    let commitment = circuit.allocate_vector_commitment();
    assert_eq!(pedersen_generators.len(), (elements.len() * 2));
    for i in 0 .. elements.len() {
      circuit.bind(
        commitment,
        circuit.variable_to_product(x_coords[i]).unwrap(),
        Some(pedersen_generators[i * 2]),
      );
      circuit.bind(
        commitment,
        circuit.variable_to_product(y_coords[i]).unwrap(),
        Some(pedersen_generators[(i * 2) + 1]),
      );
    }

    let blind = Some(if last {
      (<C::C1 as Ciphersuite>::F::ZERO, <C::C2 as Ciphersuite>::F::ZERO)
    } else {
      new_blind::<_, C::C1, C::C2>(rng)
    })
    .filter(|_| circuit.prover());
    (
      blind.map(|blind| blind.0),
      circuit.finalize_commitment(commitment, blind.map(|blind| -blind.1)),
    )
  }
}

pub fn membership_gadget<R: RngCore + CryptoRng, C: CurveCycle>(
  rng: &mut R,
  circuit_c1: &mut Circuit<C::C1>,
  circuit_c2: &mut Circuit<C::C2>,
  tree: &Tree<C>,
  blinded_point: <C::C1 as Ciphersuite>::G,
  blind: Option<(<C::C1 as Ciphersuite>::F, <C::C2 as Ciphersuite>::F)>,
) {
  let mut membership =
    blind.map(|blind| tree.membership(blinded_point + (circuit_c1.h() * blind.0)).unwrap());

  let mut blinded_point = Hash::Even(blinded_point);
  let mut even_blind = Some(blind.map(|blind| blind.1));
  let mut odd_blind = None;

  for i in 1 ..= tree.depth() {
    if (i % 2) == 1 {
      let Hash::Even(this_blinded_point) = blinded_point else {
        panic!("blinded_point was odd at odd layer")
      };

      let elems = if let Some(membership) = membership.as_mut() {
        let mut elems = vec![];
        for point in membership.remove(0) {
          let Hash::Even(point) = point else { panic!("odd layer had odd children") };
          // TODO: Ban identity from entering tree
          let (x, y) = C::c1_coords(point);
          elems.push((Some(x), Some(y)));
        }
        elems
      } else {
        vec![(None, None); tree.width()]
      };

      let (blind, point) = layer_gadget::<_, C>(
        rng,
        circuit_c2,
        circuit_c1.h(),
        tree.odd_generators(i).unwrap(),
        this_blinded_point,
        even_blind.take().unwrap(),
        elems,
        i == tree.depth(),
      );

      blinded_point = Hash::Odd(point);
      odd_blind = Some(blind);
    } else {
      let Hash::Odd(this_blinded_point) = blinded_point else {
        panic!("blinded_point was even at even layer")
      };

      let elems = if let Some(membership) = membership.as_mut() {
        let mut elems = vec![];
        for point in membership.remove(0) {
          let Hash::Odd(point) = point else { panic!("even layer had even children") };
          // TODO: Ban identity from entering tree
          let (x, y) = C::c2_coords(point);
          elems.push((Some(x), Some(y)));
        }
        elems
      } else {
        vec![(None, None); tree.width()]
      };

      let (blind, point) = layer_gadget::<_, FlipCurveCycle<C>>(
        rng,
        circuit_c1,
        circuit_c2.h(),
        tree.even_generators(i).unwrap(),
        this_blinded_point,
        odd_blind.take().unwrap(),
        elems,
        i == tree.depth(),
      );

      blinded_point = Hash::Even(point);
      even_blind = Some(blind);
    }
  }

  assert_eq!(blinded_point, tree.root());
}
