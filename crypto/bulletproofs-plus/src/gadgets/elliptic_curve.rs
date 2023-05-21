use subtle::Choice;

use ciphersuite::group::ff::{Field, PrimeField};

use crate::{
  BulletproofsCurve,
  arithmetic_circuit::{VariableReference, Constraint, Circuit},
  gadgets::bit::Bit,
};

pub trait EmbeddedShortWeierstrass: BulletproofsCurve {
  const B: u64;
}

/// Perform addition over the curve embedded into the current curve.
pub trait EmbeddedCurveAddition: BulletproofsCurve {
  /// Constrains a point to being on curve.
  fn constrain_on_curve(circuit: &mut Circuit<Self>, x: VariableReference, y: VariableReference);

  /// Doubles an on-curve point.
  fn double(
    circuit: &mut Circuit<Self>,
    x: VariableReference,
    y: VariableReference,
  ) -> (VariableReference, VariableReference);

  /// Takes in an on-curve point and another on-curve point, returning their sum.
  fn add(
    circuit: &mut Circuit<Self>,
    x1: VariableReference,
    y1: VariableReference,
    x2: VariableReference,
    y2: VariableReference,
  ) -> (VariableReference, VariableReference);

  // start is the point to perform addition onto.
  // fixed_generator is the fixed generator to perform multiplication against, and its doublings.
  // scalar is the little-endian bit decomposition.
  fn scalar_mul_generator(
    circuit: &mut Circuit<Self>,
    start_x: VariableReference,
    start_y: VariableReference,
    fixed_generator_x: &[Self::F],
    fixed_generator_y: &[Self::F],
    scalar: &[Option<Choice>],
  ) -> (VariableReference, VariableReference);

  // This is cheap to run inside the circuit, cheap enough it's not worth implementing
  // non-normalized addition.
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
  fn constrain_on_curve(circuit: &mut Circuit<Self>, x: VariableReference, y: VariableReference) {
    let ((_, _, y2_prod), _) = circuit.product(y, y);
    let (_, x2) = circuit.product(x, x);
    let ((_, _, x3), _) = circuit.product(x2, x);

    let mut constraint = Constraint::new("on-curve");
    constraint.weight(y2_prod, C::F::ONE);
    constraint.weight(x3, -C::F::ONE);
    constraint.rhs_offset(C::F::from(Self::B));
    circuit.constrain(constraint);
  }

  fn double(
    circuit: &mut Circuit<C>,
    x: VariableReference,
    y: VariableReference,
  ) -> (VariableReference, VariableReference) {
    // 1
    let (_, t0) = circuit.product(y, y);
    // 2
    let z3 = circuit.add(t0, t0);
    // 3-4
    let four = circuit.add_constant(C::F::from(4));
    let (_, z3) = circuit.product(z3, four);
    // 5, with z fixed to 1
    let t1 = y;
    // 6-7, with z fixed to 1
    let b3 = circuit.add_constant(C::F::from(C::B * 3));
    let t2 = b3;
    // 8
    let (_, x3) = circuit.product(t2, z3);
    // 9
    let y3 = circuit.add(t0, t2);
    // 10
    let (_, z3) = circuit.product(t1, z3);
    // 11-12
    let three = circuit.add_constant(C::F::from(3));
    let (_, t2) = circuit.product(t2, three);
    // 13
    let neg_one = circuit.add_constant(-C::F::ONE);
    let (_, neg_t2) = circuit.product(t2, neg_one);
    let t0 = circuit.add(t0, neg_t2);
    // 14
    let (_, y3) = circuit.product(t0, y3);
    // 15
    let y3 = circuit.add(x3, y3);
    // 16
    let (_, t1) = circuit.product(x, y);
    // 17
    let (_, x3) = circuit.product(t0, t1);
    // 18
    let two = circuit.add_constant(C::F::from(2));
    let (_, x3) = circuit.product(x3, two);

    Self::normalize(circuit, x3, y3, z3)
  }

  // Algorithm 8
  // TODO: The Curve Trees PoC peerformed this with just three constraints. Can theirs have its
  // security proven?
  // Regardless, this should be able to have its amount of constraints roughly halved re: additions
  fn add(
    circuit: &mut Circuit<C>,
    x1: VariableReference,
    y1: VariableReference,
    x2: VariableReference,
    y2: VariableReference,
  ) -> (VariableReference, VariableReference) {
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

    // 8, yet since z1 is 1, this simplifies
    let t4 = y2;
    // 9
    let t4 = circuit.add(t4, y1);
    // 10, with the same comment as 8
    let y3 = x2;
    // 11
    let y3 = circuit.add(y3, x1);

    // 12-13
    let t0_var = circuit.unchecked_variable(t0);
    let new_t0 = circuit.add_secret_input(t0_var.value().map(|t0| t0 * C::F::from(3)));
    let mut t0_constraint = Constraint::new("t0");
    t0_constraint.weight(t0_prod, C::F::from(3));
    let t0 = new_t0;

    // 14 with z1 = 1
    let t2 = b3;
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

    Self::normalize(circuit, x3, y3, z3)
  }

  // TODO: Use a table to improve the performance of this
  fn scalar_mul_generator(
    circuit: &mut Circuit<Self>,
    start_x: VariableReference,
    start_y: VariableReference,
    fixed_generator_x: &[C::F],
    fixed_generator_y: &[C::F],
    scalar: &[Option<Choice>],
  ) -> (VariableReference, VariableReference) {
    assert_eq!(fixed_generator_x.len(), usize::try_from(C::F::CAPACITY).unwrap());
    assert_eq!(fixed_generator_y.len(), usize::try_from(C::F::CAPACITY).unwrap());
    assert_eq!(scalar.len(), usize::try_from(C::F::CAPACITY).unwrap());

    let (mut curr_x, mut curr_y) = (start_x, start_y);
    for (i, bit) in scalar.iter().enumerate() {
      let bit = Bit::new(circuit, *bit);

      let (gen_x, gen_y) =
        (circuit.add_constant(fixed_generator_x[i]), circuit.add_constant(fixed_generator_y[i]));

      let (res_x, res_y) = Self::add(circuit, curr_x, curr_y, gen_x, gen_y);

      curr_x = bit.select(circuit, curr_x, res_x);
      curr_y = bit.select(circuit, curr_y, res_y);
    }

    (curr_x, curr_y)
  }
}
