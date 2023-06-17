use transcript::Transcript;
use ciphersuite::{group::ff::Field, Ciphersuite};

use crate::arithmetic_circuit::{ProductReference, Constraint, Circuit};

// Core set membership gadget, shared between the variable/constant routines.
// member should be Some if matching against a variable, None for a constant.
// value should be Some if variable + prover, Some if constant, otherwise None.
fn set_membership<T: 'static + Transcript, C: Ciphersuite>(
  circuit: &mut Circuit<T, C>,
  member: Option<ProductReference>,
  value: Option<C::F>,
  set: &[ProductReference],
) {
  assert!(set.len() >= 2);

  let sub_member = |circuit: &mut Circuit<T, C>, var| {
    let sub = if circuit.prover() {
      Some(circuit.unchecked_value(circuit.variable(var)) - value.unwrap())
    } else {
      None
    };
    circuit.add_secret_input(sub)
  };

  let mut i = 1;
  let mut accum = None;
  while i < set.len() {
    // Use the accumulator or set[0] - member
    let l = accum.unwrap_or_else(|| sub_member(circuit, set[0]));
    let r = sub_member(circuit, set[i]);
    let ((l, r, _), o_var) = circuit.product(l, r);

    let mut constrain_sub = |label, j, var| {
      let mut constraint = Constraint::new(label);
      constraint.weight(set[j], C::F::ONE);
      constraint.weight(var, -C::F::ONE);
      if let Some(member) = member {
        constraint.weight(member, -C::F::ONE);
      } else {
        constraint.rhs_offset(value.unwrap());
      }
      circuit.constrain(constraint);
    };

    // If the accumulator hasn't been created yet, this gate's lhs should be set[0] - member
    // Constrain that
    if accum.is_none() {
      constrain_sub("set_membership_l", 0, l);
    }
    constrain_sub("set_membership_r", i, r);

    accum = Some(o_var);

    i += 1;
  }

  circuit.equals_constant(circuit.variable_to_product(accum.unwrap()).unwrap(), C::F::ZERO);
}

/// Assert a variable is within a set.
pub fn assert_variable_in_set_gadget<T: 'static + Transcript, C: Ciphersuite>(
  circuit: &mut Circuit<T, C>,
  member: ProductReference,
  set: &[ProductReference],
) {
  let value =
    if circuit.prover() { Some(circuit.unchecked_value(circuit.variable(member))) } else { None };
  set_membership(circuit, Some(member), value, set);
}

/// Assert a constant is within a set.
pub fn assert_constant_in_set_gadget<T: 'static + Transcript, C: Ciphersuite>(
  circuit: &mut Circuit<T, C>,
  constant: C::F,
  set: &[ProductReference],
) {
  set_membership(circuit, None, Some(constant), set)
}

// A set membership tailored for the DLog PoK
//
// This takes in variables, asserts one of them is a constant in O(n), and returns
// ProductReferences for variable - constant.
//
// It's efficiency is by not requiring prior usage in products before performing the set
// membership.
pub(crate) fn set_with_constant<T: 'static + Transcript, C: Ciphersuite>(
  circuit: &mut Circuit<T, C>,
  constant: C::F,
  set: &[Option<C::F>],
) -> Vec<ProductReference> {
  assert!(set.len() >= 2);

  let sub_member = |circuit: &mut Circuit<T, C>, var: Option<C::F>| {
    circuit.add_secret_input(var.map(|var| var - constant))
  };

  let mut i = 1;
  let mut accum = None;
  let mut res = vec![];
  while i < set.len() {
    // Use the accumulator or set[0] - member
    let l = accum.unwrap_or_else(|| sub_member(circuit, set[0]));
    let r = sub_member(circuit, set[i]);
    let ((l, r, _), o_var) = circuit.product(l, r);

    if accum.is_none() {
      res.push(l);
    }
    res.push(r);

    accum = Some(o_var);

    i += 1;
  }

  circuit.equals_constant(circuit.variable_to_product(accum.unwrap()).unwrap(), C::F::ZERO);
  res
}
