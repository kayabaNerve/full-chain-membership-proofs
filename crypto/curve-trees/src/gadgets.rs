use ciphersuite::{group::ff::Field, Ciphersuite};

use bulletproofs_plus::{arithmetic_circuit::*, gadgets::is_non_zero_gadget};

// O(n) algorithm to find the index of an item in a list
// TODO: Remove this. At worst, we should need O(n) set presence
pub fn find_index_gadget<C: Ciphersuite>(
  circuit: &mut Circuit<C>,
  var: VariableReference,
  list: &[VariableReference],
) -> VariableReference {
  assert!(!list.is_empty());

  // Unrolled firsts loop iteration
  let value = circuit.unchecked_value(var);
  let initial_sub = value.map(|var| var - circuit.unchecked_value(list[0]).unwrap());
  let initial_sub = circuit.add_secret_input(initial_sub);
  let mut additives = vec![is_non_zero_gadget(circuit, initial_sub).variable];

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
    let sub = value.map(|var| var - circuit.unchecked_value(*item).unwrap());
    let sub = circuit.add_secret_input(sub);

    // If this is some non-zero value, force it to 1
    let normalized = is_non_zero_gadget(circuit, sub).variable;

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
    index = index.map(|index| index + circuit.unchecked_value(additive).unwrap());
  }
  let index = circuit.add_secret_input(index);

  // TODO: Merge this with other statements
  let index_prod = circuit.product(index, index).0 .0;

  constraint.weight(index_prod, -C::F::ONE);
  circuit.constrain(constraint);

  index
}
