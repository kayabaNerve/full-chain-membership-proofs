use ciphersuite::group::ff::Field;

use crate::{
  BulletproofsCurve,
  arithmetic_circuit::{VariableReference, Constraint, Circuit},
};

pub trait EmbeddedShortWeierstrass: BulletproofsCurve {
  const B: u64;
}

/// Perform addition over the curve embedded into the current curve.
pub trait EmbeddedCurveAddition: BulletproofsCurve {
  /// Takes in an on-curve point { X, Y, Z } and on-curve point { X, Y, 1 }, returning their sum.
  fn add(
    circuit: &mut Circuit<Self>,
    x1: VariableReference,
    y1: VariableReference,
    z1: VariableReference,
    x2: VariableReference,
    y2: VariableReference,
  ) -> (VariableReference, VariableReference, VariableReference);

  fn normalize(
    circuit: &mut Circuit<Self>,
    x: VariableReference,
    y: VariableReference,
    z: VariableReference,
  ) -> (VariableReference, VariableReference) {
    let z_var = circuit.unchecked_variable(z);
    let z_inv = circuit.add_secret_input(z_var.value().map(|z| z.invert().unwrap()));

    let ((_, _, one), _) = circuit.product(z, z_inv);
    let mut z_constraint = Constraint::new("z_inv");
    z_constraint.weight(one, Self::F::ONE);
    z_constraint.rhs_offset(Self::F::ONE);
    circuit.constrain(z_constraint);

    let (_, x_norm) = circuit.product(x, z_inv);
    let (_, y_norm) = circuit.product(y, z_inv);
    (x_norm, y_norm)
  }
}

// https:://eprint.iacr.org/2015/1060.pdf
impl<C: EmbeddedShortWeierstrass> EmbeddedCurveAddition for C {
  // Algorithm 8
  fn add(
    circuit: &mut Circuit<C>,
    x1: VariableReference,
    y1: VariableReference,
    z1: VariableReference,
    x2: VariableReference,
    y2: VariableReference,
  ) -> (VariableReference, VariableReference, VariableReference) {
    let b3 = circuit.add_constant(C::F::from(C::B * 3));

    // 1
    let ((_, _, t0_prod), t0) = circuit.product(x1, x2);
    // 2
    let (_, t1) = circuit.product(y1, y2);
    // 3
    let t3 = circuit.add(x2, y2);
    // 4
    let t4 = circuit.add(x1, y1);
    // 5
    let (_, t3) = circuit.product(t3, t4);

    // 6
    let t4 = circuit.add(t0, t1);

    // Obtain -t4
    let neg_one = circuit.add_constant(-C::F::ONE);
    let (_, neg_t4) = circuit.product(t4, neg_one);
    // 7
    let t3 = circuit.add(t3, neg_t4);

    // 8
    let (_, t4) = circuit.product(y2, z1);
    // 9
    let t4 = circuit.add(t4, y1);
    // 10
    let (_, y3) = circuit.product(x2, z1);
    // 11
    let y3 = circuit.add(y3, x1);

    // 12-13
    let t0_var = circuit.unchecked_variable(t0);
    let new_t0 = circuit.add_secret_input(t0_var.value().map(|t0| t0 * C::F::from(3)));
    let mut t0_constraint = Constraint::new("t0");
    t0_constraint.weight(t0_prod, C::F::from(3));
    let t0 = new_t0;

    // 14
    let (_, t2) = circuit.product(b3, z1);
    // 15
    let z3 = circuit.add(t1, t2);

    // 16
    let (_, neg_t2) = circuit.product(t2, neg_one);
    let t1 = circuit.add(t1, neg_t2);

    // 17
    let (_, y3) = circuit.product(b3, y3);
    // 18
    let (_, x3) = circuit.product(t4, y3);
    // 19
    let (_, t2) = circuit.product(t3, t1);

    // 20
    let (_, neg_x3) = circuit.product(x3, neg_one);
    let x3 = circuit.add(t2, neg_x3);

    // 21
    let ((_, t0_prod, _), y3) = circuit.product(y3, t0);
    t0_constraint.weight(t0_prod, -C::F::ONE);
    circuit.constrain(t0_constraint);

    // 22
    let (_, t1) = circuit.product(t1, z3);
    // 23
    let y3 = circuit.add(t1, y3);
    // 24
    let (_, t0) = circuit.product(t0, t3);
    // 25
    let (_, z3) = circuit.product(z3, t4);
    // 26
    let z3 = circuit.add(z3, t0);

    (x3, y3, z3)
  }
}
