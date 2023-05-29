use subtle::ConditionallySelectable;

use ciphersuite::{
  group::{
    ff::{Field, PrimeField},
    Group,
  },
  Ciphersuite,
};

use ecip::{Ecip, Poly, Divisor};
use crate::{
  arithmetic_circuit::{VariableReference, Constraint, Circuit},
  gadgets::bit::Bit,
};

pub trait EmbeddedShortWeierstrass: Ciphersuite {
  type Embedded: Ecip<FieldElement = Self::F>;

  const B: u64;
}

/// Perform operations over the curve embedded into the current curve.
pub trait EmbeddedCurveAddition: Ciphersuite {
  type Embedded: Ecip<FieldElement = Self::F>;

  /// Constrains a point to being on curve.
  fn constrain_on_curve(circuit: &mut Circuit<Self>, x: VariableReference, y: VariableReference);

  // Curve Trees, Appendix A.[4, 5]
  // This uses 4 gates theoretically, 5 as implemented here
  fn incomplete_add(
    circuit: &mut Circuit<Self>,
    x1: VariableReference,
    y1: VariableReference,
    x2: VariableReference,
    y2: VariableReference,
  ) -> (VariableReference, VariableReference) {
    let (x3, y3, slope, x2m1, x3m1) = if circuit.prover() {
      let x1_var = circuit.unchecked_variable(x1).value().unwrap();
      let y1_var = circuit.unchecked_variable(y1).value().unwrap();
      let a = Self::Embedded::from_xy(x1_var, y1_var);

      let x2_var = circuit.unchecked_variable(x2).value().unwrap();
      let y2_var = circuit.unchecked_variable(y2).value().unwrap();
      let b = Self::Embedded::from_xy(x2_var, y2_var);

      let c = a + b;

      let (x3, y3) = Self::Embedded::to_xy(c);

      let slope = (y2_var - y1_var) *
        Option::<Self::F>::from((x2_var - x1_var).invert()).expect(
          "trying to add perform incomplete addition on points which share an x coordinate",
        );

      let x2m1 = x2_var - x1_var;
      let x3m1 = x3 - x1_var;
      debug_assert_eq!(slope * x2m1, y2_var - y1_var);
      debug_assert_eq!(slope * x3m1, -y3 - y1_var);
      debug_assert_eq!(slope.square(), x1_var + x2_var + x3);

      (Some(x3), Some(y3), Some(slope), Some(x2m1), Some(x3m1))
    } else {
      (None, None, None, None, None)
    };

    let x3 = circuit.add_secret_input(x3);
    let y3 = circuit.add_secret_input(y3);
    let slope = circuit.add_secret_input(slope);
    let x2m1 = circuit.add_secret_input(x2m1);
    let x3m1 = circuit.add_secret_input(x3m1);

    let x1 = circuit.variable_to_product(x1).expect(
      "x1 wasn't prior used in a product statement. this shouldn't be possible if on-curve checked",
    );
    let y1 = circuit.variable_to_product(y1).expect(
      "y1 wasn't prior used in a product statement. this shouldn't be possible if on-curve checked",
    );
    let x2 = circuit.variable_to_product(x2).expect(
      "x2 wasn't prior used in a product statement. this shouldn't be possible if on-curve checked",
    );
    let y2 = circuit.variable_to_product(y2).expect(
      "y2 wasn't prior used in a product statement. this shouldn't be possible if on-curve checked",
    );

    // Prove x2m1 is non-zero via checking it has a multiplicative inverse, enabling incomplete
    // formulas
    let x2m1_inv = circuit.unchecked_variable(x2m1).value().map(|x2m1| x2m1.invert().unwrap());
    let x2m1_inv = circuit.add_secret_input(x2m1_inv);
    let mut constraint = Constraint::new("incomplete");
    let ((_, _, out), _) = circuit.product(x2m1, x2m1_inv);
    constraint.weight(out, Self::F::ONE);
    constraint.rhs_offset(Self::F::ONE);
    circuit.constrain(constraint);

    let ((_, x2m1, out), _) = circuit.product(slope, x2m1);
    let mut constraint = Constraint::new("slope_x2_y2_x2m1");
    constraint.weight(x2, Self::F::ONE);
    constraint.weight(x1, -Self::F::ONE);
    constraint.weight(x2m1, -Self::F::ONE);
    circuit.constrain(constraint);

    let mut constraint = Constraint::new("slope_x2_y2_out");
    constraint.weight(y2, Self::F::ONE);
    constraint.weight(y1, -Self::F::ONE);
    constraint.weight(out, -Self::F::ONE);
    circuit.constrain(constraint);

    // Use x3/y3 in a product statement so they can be used in constraints
    let ((x3_prod, y3_prod, _), _) = circuit.product(x3, y3);

    let ((_, x3m1, out), _) = circuit.product(slope, x3m1);
    let mut constraint = Constraint::new("slope_x3_y3_x3m1");
    constraint.weight(x3_prod, Self::F::ONE);
    constraint.weight(x1, -Self::F::ONE);
    constraint.weight(x3m1, -Self::F::ONE);
    circuit.constrain(constraint);

    let mut constraint = Constraint::new("slope_x3_y3_out");
    constraint.weight(y3_prod, -Self::F::ONE);
    constraint.weight(y1, -Self::F::ONE);
    constraint.weight(out, -Self::F::ONE);
    circuit.constrain(constraint);

    let ((_, _, out), _) = circuit.product(slope, slope);
    let mut constraint = Constraint::new("slope_squared");
    constraint.weight(out, -Self::F::ONE);
    constraint.weight(x1, Self::F::ONE);
    constraint.weight(x2, Self::F::ONE);
    constraint.weight(x3_prod, Self::F::ONE);
    circuit.constrain(constraint);

    (x3, y3)
  }

  fn dlog_pok(
    circuit: &mut Circuit<Self>,
    G: <Self::Embedded as Ciphersuite>::G,
    x: VariableReference,
    y: VariableReference,
    dlog: &[Bit],
  );

  /*
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
  */

  // This is cheap to run inside the circuit, cheap enough it's not worth implementing
  // non-normalized addition.
  // TODO: Is this used?
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

impl<C: EmbeddedShortWeierstrass> EmbeddedCurveAddition for C {
  type Embedded = <C as EmbeddedShortWeierstrass>::Embedded;

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

  /*
  // https:://eprint.iacr.org/2015/1060.pdf
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

  // https:://eprint.iacr.org/2015/1060.pdf, Algorithm 8
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
    let mut new_t0 = circuit.add_secret_input(t0_var.value().map(|t0| t0 * C::F::from(3)));
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
  */

  // This uses the EC IP which uses just 2.5 gates per point, beating incomplete addition.
  fn dlog_pok(
    circuit: &mut Circuit<Self>,
    G: <Self::Embedded as Ciphersuite>::G,
    known_dlog_x: VariableReference,
    y: VariableReference,
    dlog: &[Bit],
  ) {
    let CAPACITY = <Self::Embedded as Ciphersuite>::F::CAPACITY.min(Self::F::CAPACITY);
    assert_eq!(u32::try_from(dlog.len()).unwrap(), CAPACITY);

    // TODO: Move to G ** (2 ** i) to prevent needing to re-calculate these
    // TODO: Use [-1, 0, 1], or possibly a 3-bit lookup
    let mut G_pow_2 = vec![G; dlog.len()];
    for i in 1 .. dlog.len() {
      G_pow_2[i] = G_pow_2[i - 1].double();
    }

    let mut Gs = vec![];
    let mut xy_i = vec![];
    for (i, bit) in dlog.iter().enumerate() {
      if circuit.prover() {
        Gs.push(<Self::Embedded as Ciphersuite>::G::conditional_select(
          &<Self::Embedded as Ciphersuite>::G::identity(),
          &G_pow_2[i],
          bit.value.unwrap(),
        ));
      }

      let (Gx_i, Gy_i) = Self::Embedded::to_xy(G_pow_2[i]);
      let zero = circuit.add_constant(Self::F::ZERO);
      let Gx_i = circuit.add_constant(Gx_i);
      let Gy_i = circuit.add_constant(Gy_i);
      let x = bit.select(circuit, zero, Gx_i);
      let y = bit.select(circuit, zero, Gy_i);
      xy_i.push((x, y));
    }

    // These yx len checks should be the correct formulas...
    let yx_coeffs = |points| if points <= 4 { None } else { Some((points / 2) - 2) };
    let x_coeffs = |points| points / 2;

    let points = usize::try_from(CAPACITY + 1).unwrap();

    // Create the divisor
    let (divisor, y_coefficient, yx_coefficients, x_coefficients, zero_coefficient) = if circuit.prover() {
      Gs.push(-Self::Embedded::from_xy(
        circuit.unchecked_variable(known_dlog_x).value().unwrap(),
        circuit.unchecked_variable(y).value().unwrap(),
      ));
      assert_eq!(Gs.len(), points);

      // Drop all Gs which are identity
      let mut without_identity = Gs;
      {
        let mut i = 0;
        while i < without_identity.len() {
          if without_identity[i] == <Self::Embedded as Ciphersuite>::G::identity() {
            without_identity.swap_remove(i);
            continue;
          }
          i += 1;
        }
      }

      let divisor = Divisor::<Self::Embedded>::new(&without_identity);
      let Poly { y_coefficients, yx_coefficients, x_coefficients, zero_coefficient } =
        divisor.clone();
      assert!(y_coefficients.len() <= 1);
      assert_eq!(yx_coeffs(without_identity.len()), yx_coefficients.get(0).map(|vec| vec.len()));
      assert_eq!(x_coeffs(without_identity.len()), x_coefficients.len());
      assert_eq!(x_coefficients.last().unwrap(), &C::F::ONE);

      (Some(divisor), Some(y_coefficients.get(0).copied().unwrap_or(C::F::ZERO)), Some(yx_coefficients), Some(x_coefficients), Some(zero_coefficient))
    } else {
      (None, None, None, None, None)
    };

    // Add the divisor as inputs
    let y_coefficient = circuit.add_secret_input(y_coefficient);

    let mut yx_coefficients = {
      let mut vars = vec![];
      for i in 0 .. yx_coeffs(points).expect("only 2**4 points allowed?") {
        // Add Some(yx_coeff) if prover has a yx_coeff
        // Add Some(0) if prover doesn't have a yx_coeff
        // Add None if verifier
        vars.push(circuit.add_secret_input(if circuit.prover() {
          Some(
            yx_coefficients
              .as_ref()
              .unwrap()
              .get(0)
              .cloned()
              .unwrap_or(vec![])
              .get(i)
              .cloned()
              .unwrap_or(C::F::ZERO),
          )
        } else {
          None
        }));
      }
      vars
    };

    let mut x_coefficients = {
      let mut vars = vec![];
      for i in 0 .. x_coeffs(points) {
        vars.push(circuit.add_secret_input(if circuit.prover() {
          Some(x_coefficients.as_ref().unwrap().get(i).cloned().unwrap_or(C::F::ZERO))
        } else {
          None
        }));
      }
      vars
    };

    let zero_coefficient = circuit.add_secret_input(zero_coefficient);

    // Use the above coefficients in products so they can be referred to in constraints
    let mut odd = Some(y_coefficient);
    let (y_coefficient, mut x_coefficients) = {
      let mut y_coeff = None;
      let mut new_x_coeffs = vec![];
      for (i, x_coeff) in x_coefficients.drain(..).enumerate() {
        if odd.is_none() { odd = Some(x_coeff); continue; }
        let ((l, r, _), _) = circuit.product(odd.take().unwrap(), x_coeff);
        if i == 0 {
          y_coeff = Some(l);
        } else {
          new_x_coeffs.push(l);
        }
        new_x_coeffs.push(r);
      }
      (y_coeff.unwrap(), new_x_coeffs)
    };

    let mut yx_coefficients = {
      let mut new_yx_coeffs = vec![];
      for (i, yx_coeff) in yx_coefficients.drain(..).enumerate() {
        if odd.is_none() { odd = Some(yx_coeff); continue; }
        let ((l, r, _), _) = circuit.product(odd.take().unwrap(), yx_coeff);
        if i == 0 {
          x_coefficients.push(l);
        } else {
          new_yx_coeffs.push(l);
        }
        new_yx_coeffs.push(r);
      }
      new_yx_coeffs
    };

    let zero_coefficient = if let Some(odd) = odd.take() {
      let ((yx_coeff, zero_coeff, _), _) = circuit.product(odd, zero_coefficient);
      yx_coefficients.push(yx_coeff);
      zero_coeff
    } else {
      // TODO: Merge with something else
      circuit.product(zero_coefficient, zero_coefficient).0.0
    };
    assert!(odd.is_none());

    // TODO: This divisor (and the actually selected points?) needs to be committed to (equality
    // with a provided vector commitment)
    // If we need to commit to the actually selected points, we should commit to the DLog since
    // that can be done with just one mul gate/constraint via recomposing the bits

    // TODO: Select a challenge point using a hash to curve
    let challenge = C::Embedded::generator() * C::Embedded::hash_to_F(b"ecip", b"challenge");

    // Evaluate the divisor over the challenge, and over -challenge
    let (challenge_x, challenge_y) = C::Embedded::to_xy(challenge);

    // Create the powers of x
    assert!(x_coeffs(points) > yx_coeffs(points).unwrap());
    let mut x_pows = vec![challenge_x];
    while x_pows.len() < x_coeffs(points) {
      x_pows.push(*x_pows.last().unwrap() * challenge_x);
    }

    let mut lhs_constraint = Constraint::new("ecip_lhs");
    lhs_constraint.weight(zero_coefficient, C::F::ONE);

    // Perform the x_coeffs
    let mut x_res = vec![];
    for i in 0 .. x_coeffs(points) {
      lhs_constraint.weight(x_coefficients[i], x_pows[i]);
      x_res.push(circuit.unchecked_variable(circuit.variable(x_coefficients[i])).value().map(|coeff| coeff * x_pows[i]));
    }

    // Perform the yx_coeffs
    let mut neg_lhs_constraint = lhs_constraint.clone();
    let mut yx_res = vec![];
    for i in 0 .. yx_coeffs(points).unwrap() {
      let yx = challenge_y * x_pows[i];
      lhs_constraint.weight(yx_coefficients[i], yx);
      neg_lhs_constraint.weight(yx_coefficients[i], -yx);
      yx_res.push(circuit.unchecked_variable(circuit.variable(yx_coefficients[i])).value().map(|coeff| yx * coeff));
    }

    lhs_constraint.weight(y_coefficient, challenge_y);
    neg_lhs_constraint.weight(y_coefficient, -challenge_y);

    let (lhs, neg_lhs) = if circuit.prover() {
      let common = circuit.unchecked_variable(circuit.variable(zero_coefficient)).value().unwrap() + x_res.drain(..).map(Option::unwrap).sum::<C::F>();
      let yx = yx_res.drain(..).map(Option::unwrap).sum::<C::F>();
      let y = circuit.unchecked_variable(circuit.variable(y_coefficient)).value().unwrap() * challenge_y;
      (Some(common + yx + y), Some(common - yx - y))
    } else {
      (None, None)
    };
    drop(x_res);
    drop(yx_res);

    let lhs = circuit.add_secret_input(lhs);
    let neg_lhs = circuit.add_secret_input(neg_lhs);
    let ((lhs_to_constrain, neg_lhs_to_constrain, lhs), _) = circuit.product(lhs, neg_lhs);
    lhs_constraint.weight(lhs_to_constrain, -C::F::ONE);
    circuit.constrain(lhs_constraint);
    neg_lhs_constraint.weight(neg_lhs_to_constrain, -C::F::ONE);
    circuit.constrain(neg_lhs_constraint);

    if circuit.prover() {
      assert_eq!(
        circuit.unchecked_variable(circuit.variable(lhs)).value().unwrap(),
        divisor.as_ref().unwrap().eval(challenge_x, challenge_y) *
          divisor.unwrap().eval(challenge_x, -challenge_y)
      );
    }

    // TODO: Prove at least one x coefficient was 1

    // Perform the right hand side evaluation
    let one = circuit.add_constant(C::F::ONE);
    let mut accum = circuit.add_constant(C::F::ONE);
    for i in 0 .. (points - 1) {
      let this_x = circuit.add_constant(challenge_x - Self::Embedded::to_xy(G_pow_2[i]).0);
      let this_rhs = dlog[i].select(circuit, one, this_x);
      (_, accum) = circuit.product(accum, this_rhs);
    }

    let challenge_x_sub_x = circuit.add_secret_input(if circuit.prover() {
      Some(challenge_x - circuit.unchecked_variable(known_dlog_x).value().unwrap())
    } else {
      None
    });
    let ((_, challenge_x_sub_x, rhs), _) = circuit.product(accum, challenge_x_sub_x);
    let mut constraint = Constraint::new("challenge_x_sub_x");
    constraint.weight(circuit.variable_to_product(known_dlog_x).expect("point used in DLog PoK wasn't checked to be on curve"), C::F::ONE);
    constraint.weight(challenge_x_sub_x, C::F::ONE);
    constraint.rhs_offset(challenge_x);
    circuit.constrain(constraint);

    let mut constraint = Constraint::new("ecip");
    constraint.weight(lhs, C::F::ONE);
    constraint.weight(rhs, -C::F::ONE);
    circuit.constrain(constraint);
  }
}
