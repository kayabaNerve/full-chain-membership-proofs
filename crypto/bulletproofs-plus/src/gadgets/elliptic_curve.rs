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
      let x = bit.select_constant(circuit, Self::F::ZERO, Gx_i);
      let y = bit.select_constant(circuit, Self::F::ZERO, Gy_i);
      xy_i.push((x, y));
    }

    // These yx len checks should be the correct formulas...
    let yx_coeffs = |points| if points <= 4 { None } else { Some((points / 2) - 2) };
    let x_coeffs = |points| points / 2;

    let points = usize::try_from(CAPACITY + 1).unwrap();

    // Create the divisor
    let (divisor, y_coefficient, yx_coefficients, x_coefficients, zero_coefficient) =
      if circuit.prover() {
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

        (
          Some(divisor),
          Some(y_coefficients.get(0).copied().unwrap_or(C::F::ZERO)),
          Some(yx_coefficients),
          Some(x_coefficients),
          Some(zero_coefficient),
        )
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
        if odd.is_none() {
          odd = Some(x_coeff);
          continue;
        }
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
        if odd.is_none() {
          odd = Some(yx_coeff);
          continue;
        }
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
      circuit.product(zero_coefficient, zero_coefficient).0 .0
    };
    assert!(odd.is_none());

    // Prove at least one x coefficient is 1
    {
      let mut last = None;
      for x_coeff in x_coefficients.iter().skip(1).copied() {
        let lhs = if let Some(last) = last {
          last
        } else {
          circuit.add_secret_input(
            circuit
              .unchecked_variable(circuit.variable(x_coefficients[0]))
              .value()
              .map(|coeff| coeff - C::F::ONE),
          )
        };
        let rhs = circuit.add_secret_input(
          circuit
            .unchecked_variable(circuit.variable(x_coeff))
            .value()
            .map(|coeff| coeff - C::F::ONE),
        );
        let ((lhs, rhs, _), last_var) = circuit.product(lhs, rhs);

        if last.is_none() {
          let mut constraint = Constraint::new("x_coeff_0_is_1");
          constraint.weight(x_coefficients[0], C::F::ONE);
          constraint.weight(lhs, -C::F::ONE);
          constraint.rhs_offset(C::F::ONE);
          circuit.constrain(constraint);
        }

        let mut constraint = Constraint::new("x_coeff_i_is_1");
        constraint.weight(x_coeff, C::F::ONE);
        constraint.weight(rhs, -C::F::ONE);
        constraint.rhs_offset(C::F::ONE);
        circuit.constrain(constraint);

        last = Some(last_var);
      }
      let mut constraint = Constraint::new("a_x_coeff_is_1");
      constraint.weight(circuit.variable_to_product(last.unwrap()).unwrap(), C::F::ONE);
      circuit.constrain(constraint);
    }

    // TODO: This divisor (and the actually selected points) needs to be committed to (equality
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
      x_res.push(
        circuit
          .unchecked_variable(circuit.variable(x_coefficients[i]))
          .value()
          .map(|coeff| coeff * x_pows[i]),
      );
    }

    // Perform the yx_coeffs
    let mut neg_lhs_constraint = lhs_constraint.clone();
    let mut yx_res = vec![];
    for i in 0 .. yx_coeffs(points).unwrap() {
      let yx = challenge_y * x_pows[i];
      lhs_constraint.weight(yx_coefficients[i], yx);
      neg_lhs_constraint.weight(yx_coefficients[i], -yx);
      yx_res.push(
        circuit
          .unchecked_variable(circuit.variable(yx_coefficients[i]))
          .value()
          .map(|coeff| yx * coeff),
      );
    }

    lhs_constraint.weight(y_coefficient, challenge_y);
    neg_lhs_constraint.weight(y_coefficient, -challenge_y);

    let (lhs, neg_lhs) = if circuit.prover() {
      let common = circuit.unchecked_variable(circuit.variable(zero_coefficient)).value().unwrap() +
        x_res.drain(..).map(Option::unwrap).sum::<C::F>();
      let yx = yx_res.drain(..).map(Option::unwrap).sum::<C::F>();
      let y =
        circuit.unchecked_variable(circuit.variable(y_coefficient)).value().unwrap() * challenge_y;
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
      debug_assert_eq!(
        circuit.unchecked_variable(circuit.variable(lhs)).value().unwrap(),
        divisor.as_ref().unwrap().eval(challenge_x, challenge_y) *
          divisor.unwrap().eval(challenge_x, -challenge_y)
      );
    }

    // Perform the right hand side evaluation

    // Iterate over the generators' forms, either including them or using the multiplicative
    // identity if that bit wasn't set
    let mut accum = None;
    for i in 0 .. (points - 1) {
      let this_rhs = dlog[i].select_constant(
        circuit,
        C::F::ONE,
        challenge_x - Self::Embedded::to_xy(G_pow_2[i]).0,
      );
      if let Some(accum_var) = accum {
        let (_, accum_var) = circuit.product(accum_var, this_rhs);
        accum = Some(accum_var);
      } else {
        accum = Some(this_rhs);
      }
    }

    // Include the point the prover is claiming to know the DLog for
    let challenge_x_sub_x = circuit.add_secret_input(if circuit.prover() {
      Some(challenge_x - circuit.unchecked_variable(known_dlog_x).value().unwrap())
    } else {
      None
    });
    let ((_, challenge_x_sub_x, rhs), _) = circuit.product(accum.unwrap(), challenge_x_sub_x);
    let mut constraint = Constraint::new("challenge_x_sub_x");
    constraint.weight(
      circuit
        .variable_to_product(known_dlog_x)
        .expect("point used in DLog PoK wasn't checked to be on curve"),
      C::F::ONE,
    );
    constraint.weight(challenge_x_sub_x, C::F::ONE);
    constraint.rhs_offset(challenge_x);
    circuit.constrain(constraint);

    let mut constraint = Constraint::new("ecip");
    constraint.weight(lhs, C::F::ONE);
    constraint.weight(rhs, -C::F::ONE);
    circuit.constrain(constraint);
  }
}
