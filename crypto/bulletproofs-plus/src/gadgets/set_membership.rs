use ciphersuite::{group::ff::Field, Ciphersuite};

use crate::arithmetic_circuit::{ProductReference, Constraint, Circuit};

pub fn assert_set_membership_gadget<C: Ciphersuite>(
  circuit: &mut Circuit<C>,
  member: ProductReference,
  set: &[ProductReference],
) {
  assert!(set.len() >= 2);

  let value = circuit.unchecked_value(circuit.variable(member));
  let sub_member = |circuit: &mut Circuit<C>, var| {
    let sub = value.map(|value| circuit.unchecked_value(circuit.variable(var)).unwrap() - value);
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
      constraint.weight(member, -C::F::ONE);
      constraint.weight(var, -C::F::ONE);
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
