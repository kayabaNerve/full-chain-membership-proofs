use ciphersuite::group::ff::Field;

use crate::{
  BulletproofsCurve,
  arithmetic_circuit::{CheckedVariable, ProductReference, Constraint, Circuit},
};

pub trait EmbeddedShortWeierstrass: BulletproofsCurve {
  const B: u64;
}

/// Perform addition over the curve embedded into the current curve.
pub trait EmbeddedCurveAddition: BulletproofsCurve {
  /// Takes in an on-curve point { X, Y, Z } and on-curve point { X, Y, 1 }, returning their sum.
  fn add(
    circuit: &mut Circuit<Self>,
    x1: ProductReference,
    y1: ProductReference,
    z1: ProductReference,
    x2: ProductReference,
    y2: ProductReference,
  ) -> (CheckedVariable, CheckedVariable, CheckedVariable);

  fn normalize(
    circuit: &mut Circuit<Self>,
    x: CheckedVariable,
    y: CheckedVariable,
    z: CheckedVariable,
  ) -> (ProductReference, ProductReference) {
    let z_var = circuit.unchecked_variable(z.0);
    let z_inv = z_var.value().map(|z| z.invert().unwrap());
    let z_inv = circuit.add_secret_input(z_inv);
    let z_inv_product = circuit.unchecked_product(z.0, z_inv);

    // Doesn't check z since z is expected to have its checks post-added
    let mut z_constraint = Constraint::new("z_inv");
    z_constraint.weight(z_inv_product.2, Self::F::ONE);
    z_constraint.offset(Self::F::ONE);
    circuit.constrain(z_constraint);

    // Also assumes x and y have their checks post-added
    let x_norm = circuit.unchecked_product(x.0, z_inv);
    circuit.constrain_equality(z_inv_product.1, x_norm.1);

    let y_norm = circuit.unchecked_product(y.0, z_inv);
    circuit.constrain_equality(z_inv_product.1, y_norm.1);

    (x_norm.2, y_norm.2)
  }
}

// https:://eprint.iacr.org/2015/1060.pdf
impl<C: EmbeddedShortWeierstrass> EmbeddedCurveAddition for C {
  // Algorithm 8
  fn add(
    circuit: &mut Circuit<C>,
    x1: ProductReference,
    y1: ProductReference,
    z1: ProductReference,
    x2: ProductReference,
    y2: ProductReference,
  ) -> (CheckedVariable, CheckedVariable, CheckedVariable) {
    let b3 = circuit.add_constant(C::F::from(C::B * 3));

    // 1
    let t0 = circuit.product(x1, x2);
    // 2
    let t1 = circuit.product(y1, y2);
    // 3
    let t3 = circuit.add(x2, y2);
    // 4
    let t4 = circuit.add(x1, y1);

    // 5
    // Unchecked since the additions post-add their constraints
    let (_, _, t3) = circuit.unchecked_product(t3.0, t4.0);

    // 6
    let t4 = circuit.add(t0, t1);

    // Obtain -t4
    // Unchecked since the addition will post-add its constraint, after we perform this product,
    // and because the constant is similarly checked
    let neg_one_const = circuit.add_constant(-C::F::ONE);
    let (_, neg_one, neg_t4) = circuit.unchecked_product(t4.0, neg_one_const.0);
    // 7
    let t3 = circuit.add(t3, neg_t4);

    // 8
    let t4 = circuit.product(y2, z1);
    // 9
    let t4 = circuit.add(t4, y1);
    // 10
    let y3 = circuit.product(x2, z1);
    // 11
    let y3 = circuit.add(y3, x1);

    // 12-13
    // Doesn't use x3, saves a constraint, safe since x3 has no further usage till re-assignment
    let t0_ref = circuit.product_to_unchecked_variable(t0);
    let t0_var = circuit.unchecked_variable(t0_ref);
    let new_t0 = circuit.add_secret_input(t0_var.value().map(|t0| t0 * C::F::from(3)));
    let mut t0_constraint = Constraint::new("t0");
    t0_constraint.weight(t0, C::F::from(3));
    // t0_constraint is completed after t0 is used in a product
    let t0 = new_t0;

    // 14
    // b3 will have the constraint added automatically
    let z1_var = circuit.product_to_unchecked_variable(z1);
    let (_, unchecked_z1, t2) = circuit.unchecked_product(b3.0, z1_var);
    circuit.constrain_equality(unchecked_z1, z1);

    // 15
    let z3 = circuit.add(t1, t2);

    // 16
    let neg_t2 = circuit.product(t2, neg_one);
    let t1 = circuit.add(t1, neg_t2);

    // 17
    // Safe due to post-addition of constraints for const/add
    let y3 = circuit.unchecked_product(b3.0, y3.0).2;

    // 18
    // t4 is an addition result and accordingly safe
    let y3_var = circuit.product_to_unchecked_variable(y3);
    let x3 = circuit.unchecked_product(t4.0, y3_var);
    circuit.constrain_equality(x3.1, y3);
    let x3 = x3.2;

    // 19
    // Safe since t3/t1 have constraints post-added
    let t2 = circuit.unchecked_product(t3.0, t1.0).2;

    // 20
    let neg_x3 = circuit.product(x3, neg_one);
    let x3 = circuit.add(t2, neg_x3);

    // 21
    let new_y3 = circuit.unchecked_product(y3_var, t0);
    let t0_product_ref = new_y3.1;
    t0_constraint.weight(t0_product_ref, -C::F::ONE);
    circuit.constrain(t0_constraint);
    circuit.constrain_equality(y3, new_y3.0);
    let y3 = new_y3.2;

    // 22
    // Safe due to adding addition results
    let t1 = circuit.unchecked_product(t1.0, z3.0).2;

    // 23
    let y3 = circuit.add(t1, y3);

    // 24
    // t3 i an addition result and safe. t0 needs a constraint
    let t0 = circuit.unchecked_product(t0, t3.0);
    circuit.constrain_equality(t0.0, t0_product_ref);
    let t0 = t0.2;

    // 25
    // Safe due to adding addition results
    let z3 = circuit.unchecked_product(z3.0, t4.0).2;
    // 26
    let z3 = circuit.add(z3, t0);

    (x3, y3, z3)
  }
}
