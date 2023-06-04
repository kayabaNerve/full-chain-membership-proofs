use ciphersuite::{group::ff::Field, Ciphersuite};

use bulletproofs_plus::arithmetic_circuit::*;

pub fn assert_non_zero_gadget<C: Ciphersuite>(circuit: &mut Circuit<C>, var: VariableReference) {
  // Assert this wasn't zero by checking a multiplicative inverse exists
  let inv = circuit.unchecked_variable(var).value().map(|val| val.invert().unwrap());
  let inv = circuit.add_secret_input(inv);
  let ((_, _, one), _) = circuit.product(var, inv);
  circuit.equals_constant(one, C::F::ONE);
}

// Returns a variable for 1 if the value is non-zero, or a variable for 0 if the value is 0
pub fn is_non_zero_gadget<C: Ciphersuite>(
  circuit: &mut Circuit<C>,
  var: VariableReference,
) -> VariableReference {
  // Multiply against the inverse, or 1 if there is no inverse due to this being 0
  // This makes the output 0/1 for an honest prover
  let inv = circuit.unchecked_variable(var).value().map(|val| val.invert().unwrap_or(C::F::ONE));
  let inv = circuit.add_secret_input(inv);
  let ((_, _, _), out) = circuit.product(var, inv);

  // Ensure this provided inverse wasn't 0
  // If it wasn't 0, `out` will only be 0 if var was 0. If var was non-zero, it'll be non-zero
  assert_non_zero_gadget(circuit, inv);

  // Now verify the output is 1 or 0, since an opportunity was provided to so normalize yet it
  // may not have actually been normalized
  {
    let minus_one = circuit.unchecked_variable(out).value().map(|val| val - C::F::ONE);
    let minus_one = circuit.add_secret_input(minus_one);
    let ((out, minus_one, zero), _) = circuit.product(out, minus_one);

    let mut constraint = Constraint::new("minus_one");
    constraint.weight(out, C::F::ONE);
    constraint.weight(minus_one, -C::F::ONE);
    constraint.rhs_offset(C::F::ONE);
    circuit.constrain(constraint);

    circuit.equals_constant(zero, C::F::ZERO);
  }

  out
}

// O(n) algorithm to find the index of an item in a list
// TODO: Remove this. At worst, we should need O(n) set presence
pub fn find_index_gadget<C: Ciphersuite>(
  circuit: &mut Circuit<C>,
  var: VariableReference,
  list: &[VariableReference],
) -> VariableReference {
  assert!(!list.is_empty());

  // Unrolled firsts loop iteration
  let value = circuit.unchecked_variable(var).value();
  let initial_sub = value.map(|var| var - circuit.unchecked_variable(list[0]).value().unwrap());
  let initial_sub = circuit.add_secret_input(initial_sub);
  let mut additives = vec![is_non_zero_gadget(circuit, initial_sub)];

  let sub_constraint = |circuit: &mut Circuit<_>, label, item, res| {
    let mut sub_constraint = Constraint::new(label);
    sub_constraint.weight(circuit.variable_to_product(var).unwrap(), C::F::ONE);
    sub_constraint.weight(circuit.variable_to_product(item).unwrap(), -C::F::ONE);
    sub_constraint.weight(circuit.variable_to_product(res).unwrap(), -C::F::ONE);
    circuit.constrain(sub_constraint);
  };
  sub_constraint(circuit, "initial_sub", list[0], initial_sub);

  for item in list.iter().skip(1) {
    // If the variable - item is 0, then this is the variable
    let sub = value.map(|var| var - circuit.unchecked_variable(*item).value().unwrap());
    let sub = circuit.add_secret_input(sub);

    // If this is some non-zero value, force it to 1
    let normalized = is_non_zero_gadget(circuit, sub);

    sub_constraint(circuit, "sub", *item, sub);

    // Multiply additive by the normalized value
    // This means the additive variable is 1 until we find the item, and 0 after
    additives.push(circuit.product(*additives.last().unwrap(), normalized).1);
  }

  // Make sure this item was actually present in the list
  circuit
    .equals_constant(circuit.variable_to_product(*additives.last().unwrap()).unwrap(), C::F::ZERO);

  // Sum additives to determine the index
  let mut index = Some(C::F::ZERO).filter(|_| circuit.prover());
  let mut constraint = Constraint::new("index");
  for additive in additives {
    constraint.weight(circuit.variable_to_product(additive).unwrap(), C::F::ONE);
    index = index.map(|index| index + circuit.unchecked_variable(additive).value().unwrap());
  }
  let index = circuit.add_secret_input(index);

  // TODO: Merge this with other statements
  let index_prod = circuit.product(index, index).0 .0;

  constraint.weight(index_prod, -C::F::ONE);
  circuit.constrain(constraint);

  index
}
