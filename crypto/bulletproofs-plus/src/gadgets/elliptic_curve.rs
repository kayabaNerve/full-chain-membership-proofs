use rand_core::{RngCore, CryptoRng};

use subtle::ConditionallySelectable;

use ciphersuite::{
  group::{
    ff::{Field, PrimeField},
    Group, GroupEncoding,
  },
  Ciphersuite,
};

use ecip::{Ecip, Poly, Divisor};

use crate::{
  arithmetic_circuit::{VariableReference, Constraint, Circuit},
  gadgets::{Bit, assert_non_zero_gadget, set_membership::assert_set_membership_gadget},
};

/// An on-curve point which is not identity.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct OnCurvePoint {
  x: VariableReference,
  y: VariableReference,
}

impl OnCurvePoint {
  pub fn x(&self) -> VariableReference {
    self.x
  }
  pub fn y(&self) -> VariableReference {
    self.y
  }
}

/// A table for efficient proofs of knowledge of DLog.
pub struct DLogTable<C: Ciphersuite>(Vec<C::G>);
impl<C: Ciphersuite> DLogTable<C> {
  pub fn new(point: C::G) -> DLogTable<C> {
    assert!(point != C::G::identity());

    // TODO: Use a more efficient table
    let bits = usize::try_from(C::F::CAPACITY).unwrap();
    let mut G_pow_2 = vec![point; bits];
    for i in 1 .. bits {
      G_pow_2[i] = G_pow_2[i - 1].double();
    }
    DLogTable(G_pow_2)
  }

  pub fn generator(&self) -> C::G {
    self.0[0]
  }
}

/// Perform operations over the curve embedded into the proof's curve.
pub trait EmbeddedCurveOperations: Ciphersuite {
  type Embedded: Ecip<FieldElement = Self::F>;

  /// Constrains a point to being on curve AND not being the identity.
  fn constrain_on_curve(
    circuit: &mut Circuit<Self>,
    x: VariableReference,
    y: VariableReference,
  ) -> OnCurvePoint;

  /// Performs addition between two points, where P1 != P2, P1 != -P2, and neither P1 nor P2 are
  /// identity.
  ///
  /// The only checks performed by this function is P1 != P2 and P1 != -P2. Neither point is
  /// checked to not be identity.

  // Curve Trees, Appendix A.[4, 5]
  // This uses 4 gates theoretically, 5 as implemented here, and 6 constraints
  fn incomplete_add(
    circuit: &mut Circuit<Self>,
    p1: OnCurvePoint,
    p2: OnCurvePoint,
  ) -> OnCurvePoint {
    let OnCurvePoint { x: x1, y: y1 } = p1;
    let OnCurvePoint { x: x2, y: y2 } = p2;

    let (x3, y3, slope, x2m1, x3m1) = if circuit.prover() {
      let x1_var = circuit.unchecked_value(x1).unwrap();
      let y1_var = circuit.unchecked_value(y1).unwrap();
      let a = Self::Embedded::from_xy(x1_var, y1_var);

      let x2_var = circuit.unchecked_value(x2).unwrap();
      let y2_var = circuit.unchecked_value(y2).unwrap();
      let b = Self::Embedded::from_xy(x2_var, y2_var);

      let c = a + b;

      let (x3, y3) = Self::Embedded::to_xy(c);

      let slope = (y2_var - y1_var) *
        Option::<Self::F>::from((x2_var - x1_var).invert()).expect(
          "trying to add perform incomplete addition on points which share an x coordinate",
        );

      let x2m1 = x2_var - x1_var;
      let x3m1 = x3 - x1_var;

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

    // Prove x2m1 is non-zero, meaning x2 != x1, enabling incomplete formulas
    assert_non_zero_gadget(circuit, x2m1);

    // Constrain x2m1 is correct
    let mut constraint = Constraint::new("x2m1");
    constraint.weight(x2, Self::F::ONE);
    constraint.weight(x1, -Self::F::ONE);
    // Safe since the non-zero gadget will use it in a product statement
    constraint.weight(circuit.variable_to_product(x2m1).unwrap(), -Self::F::ONE);
    circuit.constrain(constraint);

    // A.4 (6)
    {
      let ((_, _, slope_x2m1), _) = circuit.product(slope, x2m1);
      // slope_x2m1 - (y2 - y1) == 0
      let mut constraint = Constraint::new("slope_x2m1");
      constraint.weight(slope_x2m1, Self::F::ONE);
      constraint.weight(y2, -Self::F::ONE);
      constraint.weight(y1, Self::F::ONE);
      circuit.constrain(constraint);
    }

    // Use x3/y3 in a product statement so they can be used in constraints
    // TODO: Design around this internally
    let ((x3_prod, y3_prod, _), _) = circuit.product(x3, y3);

    // A.4 (7)
    {
      let ((_, x3m1, slope_x3m1), _) = circuit.product(slope, x3m1);

      // Constrain x3m1's accuracy
      {
        let mut constraint = Constraint::new("x3m1");
        constraint.weight(x3_prod, Self::F::ONE);
        constraint.weight(x1, -Self::F::ONE);
        constraint.weight(x3m1, -Self::F::ONE);
        circuit.constrain(constraint);
      }

      // slope_x3m1 - (-y3 - y1) == 0
      let mut constraint = Constraint::new("slope_x3m1");
      constraint.weight(slope_x3m1, Self::F::ONE);
      constraint.weight(y3_prod, Self::F::ONE);
      constraint.weight(y1, Self::F::ONE);
      circuit.constrain(constraint);
    }

    // A.4 (8)
    {
      let ((_, _, slope_squared), _) = circuit.product(slope, slope);

      // 0 == x1 + x2 + x3 - slope_squared
      let mut constraint = Constraint::new("slope_squared");
      constraint.weight(slope_squared, -Self::F::ONE);
      constraint.weight(x3_prod, Self::F::ONE);
      constraint.weight(x1, Self::F::ONE);
      constraint.weight(x2, Self::F::ONE);
      circuit.constrain(constraint);
    }

    OnCurvePoint { x: x3, y: y3 }
  }

  // This uses the EC IP which uses just 2 gates per point, plus 2, beating incomplete addition
  // As currently implemented (with an inefficiency) it's 3 gates per point
  //
  // TODO: Due to the vector commitment scheme currently implemented, each gate causes six extra
  // gates in distinct proofs (two gates per item, three items per gate (left, right, output)).
  // That means this uses 14 gates per point
  // If a zero-cost vector commitment scheme isn't implemented, this isn't worth it
  //
  // Gate count is notated GC
  fn dlog_pok<R: RngCore + CryptoRng>(
    rng: &mut R,
    circuit: &mut Circuit<Self>,
    G: &DLogTable<Self::Embedded>,
    p: OnCurvePoint,
    dlog: &[Bit],
  ) {
    let CAPACITY = <Self::Embedded as Ciphersuite>::F::CAPACITY.min(Self::F::CAPACITY);
    assert_eq!(u32::try_from(dlog.len()).unwrap(), CAPACITY);

    // TODO: Use [-1, 0, 1], or possibly a 3-bit lookup
    let Gs = if circuit.prover() {
      let mut Gs = vec![];
      for (i, bit) in dlog.iter().enumerate() {
        Gs.push(<Self::Embedded as Ciphersuite>::G::conditional_select(
          &<Self::Embedded as Ciphersuite>::G::identity(),
          &G.0[i],
          bit.value.unwrap(),
        ));
      }
      Some(Gs)
    } else {
      None
    };

    // These yx len checks should be the correct formulas...
    let yx_coeffs = |points| if points <= 4 { None } else { Some((points / 2) - 2) };
    let x_coeffs = |points| points / 2;

    let points = usize::try_from(CAPACITY + 1).unwrap();

    // Create the divisor
    let (y_coefficient, yx_coefficients, x_coefficients, zero_coefficient) = if circuit.prover() {
      let mut Gs = Gs.unwrap();
      Gs.push(-Self::Embedded::from_xy(
        circuit.unchecked_value(p.x).unwrap(),
        circuit.unchecked_value(p.y).unwrap(),
      ));
      assert_eq!(Gs.len(), points);

      // Drop all Gs which are identity
      let mut without_identity = Gs;
      {
        let mut i = 0;
        while i < without_identity.len() {
          if without_identity[i].is_identity().into() {
            without_identity.swap_remove(i);
            continue;
          }
          i += 1;
        }
      }

      let divisor = Divisor::<Self::Embedded>::new(&without_identity);
      let Poly { y_coefficients, yx_coefficients, x_coefficients, zero_coefficient } = divisor;
      assert!(y_coefficients.len() <= 1);
      assert_eq!(yx_coeffs(without_identity.len()), yx_coefficients.get(0).map(|vec| vec.len()));
      assert_eq!(x_coeffs(without_identity.len()), x_coefficients.len());
      assert_eq!(x_coefficients.last().unwrap(), &Self::F::ONE);

      (
        Some(y_coefficients.get(0).copied().unwrap_or(Self::F::ZERO)),
        Some(yx_coefficients),
        Some(x_coefficients),
        Some(zero_coefficient),
      )
    } else {
      (None, None, None, None)
    };

    // Add the divisor into the circuit, creating a transcript of it
    // GC: 0.5 per point
    let (mut transcript, y_coefficient, yx_coefficients, x_coefficients, zero_coefficient) = {
      // First, create a serial representation of the divisor
      let mut serial_divisor = {
        let mut serial_divisor = vec![y_coefficient];
        for i in
          0 .. yx_coeffs(points).expect("only 2**4 points were allowed for this composition?")
        {
          // Add Some(yx_coeff) if prover has a yx_coeff
          // Add Some(0) if prover doesn't have a yx_coeff
          // Add None if verifier
          serial_divisor.push(if circuit.prover() {
            Some(
              yx_coefficients
                .as_ref()
                .unwrap()
                .get(0)
                .cloned()
                .unwrap_or(vec![])
                .get(i)
                .cloned()
                .unwrap_or(Self::F::ZERO),
            )
          } else {
            None
          });
        }

        for i in 0 .. x_coeffs(points) {
          serial_divisor.push(if circuit.prover() {
            Some(x_coefficients.as_ref().unwrap().get(i).cloned().unwrap_or(Self::F::ZERO))
          } else {
            None
          });
        }

        serial_divisor.push(zero_coefficient);
        serial_divisor
      };

      // Next, add all of the vars in circuit
      let serial_divisor =
        serial_divisor.drain(..).map(|e| circuit.add_secret_input(e)).collect::<Vec<_>>();

      // Use each variable in a product to enable their usage in constraints
      let serial_divisor = {
        let mut i = 0;
        let mut products = vec![];
        while i < serial_divisor.len() {
          let l = serial_divisor[i];
          let r = serial_divisor.get(i + 1).copied();

          // TODO: Merge the tail case with something else
          let (l, r_prod, _) = circuit.product(l, r.unwrap_or(l)).0;
          products.push(l);
          if r.is_some() {
            products.push(r_prod);
          }

          i += 2;
        }

        products
      };

      // Decompose the serial divisor back to its components
      let mut iter = serial_divisor.iter().cloned();
      let y_coefficient = iter.next().unwrap();
      let mut yx_coefficients = vec![];
      let mut x_coefficients = vec![];
      while x_coefficients.len() < x_coeffs(points) {
        if yx_coefficients.len() < yx_coeffs(points).unwrap() {
          yx_coefficients.push(iter.next().unwrap());
          continue;
        }
        x_coefficients.push(iter.next().unwrap());
      }
      let zero_coefficient = iter.next().unwrap();
      assert!(iter.next().is_none());
      (serial_divisor, y_coefficient, yx_coefficients, x_coefficients, zero_coefficient)
    };

    // Prove at least one x coefficient is 1

    // This is a O(n) algorithm since the polynomial is of variable length, and the highest-order
    // term is the one with a coefficient of 1
    //
    // We can normalize so the lowest-order term has a coefficient of 1, yet it'd make some
    // divisors unrepresentable. Doing so would speed this up 40%, and worth it if said divisors
    // are negligible (divisors for when only two bits in the scalar were set)
    //
    // Alternatively, a distinct method for proving the divisor isn't identical to zero may be
    // viable
    //
    // TODO

    // GC: 0.5 per point + 1
    let one = circuit.add_secret_input(Some(Self::F::ONE).filter(|_| circuit.prover()));
    let one = circuit.product(one, one).0 .0;
    assert_set_membership_gadget(circuit, one, &x_coefficients);

    // Also transcript the DLog
    for bit in dlog {
      // TODO: This requires the DLog bit not be prior bound. How safe is that?
      // Note: We can only bind a single element, the re-composition of the DLog, if desirable
      // It'd be a single sharable gate and one constraint
      transcript.push(circuit.variable_to_product(bit.variable).unwrap());
    }

    // The transcript is defined as a series of variables in gates
    // Put these into a dedicated commitment so we can use the commitment for challenges
    let commitment = circuit.allocate_vector_commitment();
    for var in transcript {
      circuit.bind(commitment, var, None);
    }
    let commitment = circuit
      .finalize_commitment(commitment, Some(Self::F::random(rng)).filter(|_| circuit.prover()));

    let challenge = Self::Embedded::hash_to_G("bp+_ecip", commitment.to_bytes().as_ref());

    // Evaluate the divisor over the challenge, and over -challenge
    let (challenge_x, challenge_y) = Self::Embedded::to_xy(challenge);

    // Create the powers of x
    assert!(x_coeffs(points) > yx_coeffs(points).unwrap());
    let mut x_pows = vec![challenge_x];
    while x_pows.len() < x_coeffs(points) {
      x_pows.push(*x_pows.last().unwrap() * challenge_x);
    }

    let mut lhs_constraint = Constraint::new("ecip_lhs");
    lhs_constraint.weight(zero_coefficient, Self::F::ONE);

    // Perform the x_coeffs
    let mut x_res = vec![];
    for i in 0 .. x_coeffs(points) {
      lhs_constraint.weight(x_coefficients[i], x_pows[i]);
      x_res.push(
        circuit.unchecked_value(circuit.variable(x_coefficients[i])).map(|coeff| coeff * x_pows[i]),
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
        circuit.unchecked_value(circuit.variable(yx_coefficients[i])).map(|coeff| yx * coeff),
      );
    }

    lhs_constraint.weight(y_coefficient, challenge_y);
    neg_lhs_constraint.weight(y_coefficient, -challenge_y);

    let (lhs, neg_lhs) = if circuit.prover() {
      let common = circuit.unchecked_value(circuit.variable(zero_coefficient)).unwrap() +
        x_res.drain(..).map(Option::unwrap).sum::<Self::F>();
      let yx = yx_res.drain(..).map(Option::unwrap).sum::<Self::F>();
      let y = circuit.unchecked_value(circuit.variable(y_coefficient)).unwrap() * challenge_y;
      (Some(common + yx + y), Some(common - yx - y))
    } else {
      (None, None)
    };
    drop(x_res);
    drop(yx_res);

    let lhs = circuit.add_secret_input(lhs);
    let neg_lhs = circuit.add_secret_input(neg_lhs);
    // GC: 1
    let ((lhs_to_constrain, neg_lhs_to_constrain, lhs), _) = circuit.product(lhs, neg_lhs);
    lhs_constraint.weight(lhs_to_constrain, -Self::F::ONE);
    circuit.constrain(lhs_constraint);
    neg_lhs_constraint.weight(neg_lhs_to_constrain, -Self::F::ONE);
    circuit.constrain(neg_lhs_constraint);

    // Perform the right hand side evaluation

    // Iterate over the generators' forms, either including them or using the multiplicative
    // identity if that bit wasn't set

    // GC: 2 per point, 1 if we inline select_constant
    let mut accum = None;
    for (bit, G) in dlog.iter().zip(G.0.iter()).take(points - 1) {
      let this_rhs =
        bit.select_constant(circuit, Self::F::ONE, challenge_x - Self::Embedded::to_xy(*G).0);
      if let Some(accum_var) = accum {
        let (_, accum_var) = circuit.product(accum_var, this_rhs);
        accum = Some(accum_var);
      } else {
        accum = Some(this_rhs);
      }
    }

    // Include the point the prover is claiming to know the DLog for
    let challenge_x_sub_x = circuit.add_secret_input(if circuit.prover() {
      Some(challenge_x - circuit.unchecked_value(p.x).unwrap())
    } else {
      None
    });
    // GC: 1
    let ((_, challenge_x_sub_x, rhs), _) = circuit.product(accum.unwrap(), challenge_x_sub_x);
    let mut constraint = Constraint::new("challenge_x_sub_x");
    constraint.weight(
      circuit
        .variable_to_product(p.x)
        .expect("point used in DLog PoK wasn't checked to be on curve"),
      Self::F::ONE,
    );
    constraint.weight(challenge_x_sub_x, Self::F::ONE);
    constraint.rhs_offset(challenge_x);
    circuit.constrain(constraint);

    let mut constraint = Constraint::new("ecip");
    constraint.weight(lhs, Self::F::ONE);
    constraint.weight(rhs, -Self::F::ONE);
    circuit.constrain(constraint);
  }
}

pub trait EmbeddedShortWeierstrass: Ciphersuite {
  type Embedded: Ecip<FieldElement = Self::F>;

  const B: u64;
}

impl<C: EmbeddedShortWeierstrass> EmbeddedCurveOperations for C {
  type Embedded = <C as EmbeddedShortWeierstrass>::Embedded;

  // y**2 = x**3 + B
  fn constrain_on_curve(
    circuit: &mut Circuit<Self>,
    x: VariableReference,
    y: VariableReference,
  ) -> OnCurvePoint {
    let ((_, _, y2_prod), _) = circuit.product(y, y);
    let (_, x2) = circuit.product(x, x);
    let ((_, _, x3), _) = circuit.product(x2, x);

    let mut constraint = Constraint::new("on-curve");
    constraint.weight(y2_prod, Self::F::ONE);
    constraint.weight(x3, -Self::F::ONE);
    constraint.rhs_offset(Self::F::from(Self::B));
    circuit.constrain(constraint);

    OnCurvePoint { x, y }
  }
}
