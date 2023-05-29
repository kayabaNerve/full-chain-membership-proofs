use subtle::{Choice, ConditionallySelectable};

use ciphersuite::{group::ff::Field, Ciphersuite};

use crate::arithmetic_circuit::{VariableReference, Constraint, Circuit};

#[derive(Clone, Copy, Debug)]
pub struct Bit {
  pub value: Option<Choice>,
  pub variable: VariableReference,
  pub minus_one: VariableReference,
}

impl Bit {
  pub fn new<C: Ciphersuite>(circuit: &mut Circuit<C>, choice: Option<Choice>) -> Bit {
    let bit = choice.map(|choice| C::F::from(u64::from(choice.unwrap_u8())));

    let l = circuit.add_secret_input(bit);
    let r = circuit.add_secret_input(bit.map(|bit| bit - C::F::ONE));

    // Verify this is in fact a valid bit
    // TODO: Can this be reduced to a single constraint?
    {
      let ((l_prod, r_prod, o_prod), _) = circuit.product(l, r);

      // Force the output to be 0, meaning one of factors has to be 0
      let mut bit_product = Constraint::new("bit_product");
      bit_product.weight(o_prod, C::F::ONE);
      circuit.constrain(bit_product);

      // l + -r = 1
      // One must be 0
      // If l is 0, the only solution for r is -1
      // If r is 0, the only solution for l is 1
      let mut l_minus_one = Constraint::new("l_minus_one");
      l_minus_one.weight(l_prod, C::F::ONE);
      l_minus_one.weight(r_prod, -C::F::ONE);
      l_minus_one.rhs_offset(C::F::ONE);
      circuit.constrain(l_minus_one);
    }

    Bit { value: choice, variable: l, minus_one: r }
  }

  pub fn select<C: Ciphersuite>(
    &self,
    circuit: &mut Circuit<C>,
    if_false: VariableReference,
    if_true: VariableReference,
  ) -> VariableReference {
    let false_var = circuit.unchecked_variable(if_false).value();
    let true_var = circuit.unchecked_variable(if_true).value();
    let chosen = Some(()).filter(|_| circuit.prover()).map(|_| {
      C::F::conditional_select(&false_var.unwrap(), &true_var.unwrap(), self.value.unwrap())
    });

    let chosen = circuit.add_secret_input(chosen);

    // TODO: Merge this product statements with others
    let ((chosen_prod, _, _), _) = circuit.product(chosen, chosen);

    // (bit * if_true) + (-bit_minus_one * if_false)
    // If bit is 0, if_false. If bit is 1, if_true
    let ((_, _, lo), _) = circuit.product(self.variable, if_true);
    let ((_, _, ro), _) = circuit.product(self.minus_one, if_false);
    let mut chosen_constraint = Constraint::new("chosen");
    chosen_constraint.weight(lo, C::F::ONE);
    chosen_constraint.weight(ro, -C::F::ONE);
    chosen_constraint.weight(chosen_prod, -C::F::ONE);
    circuit.constrain(chosen_constraint);

    chosen
  }

  pub fn select_constant<C: Ciphersuite>(
    &self,
    circuit: &mut Circuit<C>,
    if_false: C::F,
    if_true: C::F,
  ) -> VariableReference {
    let chosen = Some(())
      .filter(|_| circuit.prover())
      .map(|_| C::F::conditional_select(&if_false, &if_true, self.value.unwrap()));

    let chosen = circuit.add_secret_input(chosen);

    // TODO: Merge this product statements with others
    let ((chosen_prod, _, _), _) = circuit.product(chosen, chosen);
    let mut chosen_constraint = Constraint::new("chosen");
    // If bit, lhs = if_true
    // If !bit, lhs = if_false
    chosen_constraint.weight(circuit.variable_to_product(self.variable).unwrap(), if_true);
    chosen_constraint.weight(circuit.variable_to_product(self.minus_one).unwrap(), -if_false);
    chosen_constraint.weight(chosen_prod, -C::F::ONE);
    circuit.constrain(chosen_constraint);

    chosen
  }
}
