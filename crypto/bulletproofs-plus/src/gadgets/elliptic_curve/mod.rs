use rand_core::{RngCore, CryptoRng};

use subtle::Choice;

use transcript::Transcript;
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
  gadgets::{Bit, assert_non_zero_gadget, set_membership::set_with_constant},
};

mod trinary;
pub use trinary::*;

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

/// A table for efficient proofs of knowledge of discrete logarithms over a specified generator.

/*
  Creating a bit takes one gate. Selecting a zero-knowledge variable takes one gate.

  The current DLog PoK takes in 255 bits (each costing 1 gate to be created each) and performs
  addition for 255 points, each addition costing 1.75 gates. This means without tabling, the DLog
  PoK costs 255 + (255 * 1.75) = 701.25 gates.

  If we created 3-wide tables, we'd need 2 bits to perform the selection (1 bit for 0 or 1, 1 bit
  for the result of the prior operation or 2). This not only adds a gate to create the second bit,
  yet also one for the second selection (which is ZK or constant). This would be (2 * 255) +
  (161 * 1.75) = 791.75 gates.

  If we used a 3-set membership, it would only take n - 1 gates, AKA 2 gates. This would be
  ((3 - 1) * 161) + (1.75 * 161) = 603.75 gates. Unfortunately, the DLog PoK gadget cannot be laid
  out as compatible with set membership (TODO: Further work on this?).

  The DLog PoK works by creating a divisor which interpolates a series of points which sum to 0.
  Notably, we only check their x coordinates interpolate to 0. This allows malleability.

  Instead of proving A + B + C = 0, a 'malicious' prover can prove A - B + C sums to 0.
  This isn't an issue as anyone who knows the DLog with negatives can calculate the DLog without
  negatives. Therefore, knowledge of the DLog with negatives implies knowledge of the DLog without
  them.

  We take advantage of this by proving knowledge of some sum of G*3**i. Using a trinary system of
  [-1, 0, 1], we can prove a 2**256 DLog in just 161 points with just 161 bits for selections.

  3 ** 161 ~= 2 ** 256
  161 + (1.75 * 161) = 442.75

  TODO: The curve trees paper describes a 3-bit lookup with just 5 gates, beating the above
  commentary which was n - 1.

  2 ** 3 = 8
  The set of 0G ..= 7G + -(0G ..= 7G) has 15 elements.
  15 ** 65 ~= 2 ** 256
  (5 * 65) + (1.75 * 65) = 438.75

  We'd save 4 gates by implementing it.

  If a 2-bit lookup can be done with three gates, it'd save 10 gates. It'd save 101 if it can be
  done with just two gates. Arkwork's implementativon uses three gates.
*/
// TODO: Transcript this
pub struct DLogTable<C: Ecip>(Vec<C::G>, usize);
impl<C: Ecip> DLogTable<C> {
  pub fn new(point: C::G) -> DLogTable<C> {
    assert!(point != C::G::identity());

    // Mutual amount of bits
    // TODO: This assumes this is being used in a cycle, not a tower
    let CAPACITY = C::F::CAPACITY.min(C::FieldElement::CAPACITY);
    // Maximum value representable in this mutual amount of bits
    let max = C::F::from(2).pow([u64::from(CAPACITY)]) - C::F::ONE;
    // Trits needed for this maximum value
    // TODO: Technically, this is a bit indirect
    // It should be the amount of trits which will fit into both fields, not the amount of trits
    // which will fit into the mutual capacity of both fields
    let trits = scalar_to_trits::<C>(max).len();
    let mut G_pow_3 = vec![point; trits];
    for i in 1 .. trits {
      G_pow_3[i] = G_pow_3[i - 1].double() + G_pow_3[i - 1];
    }
    DLogTable(G_pow_3, trits)
  }

  pub fn trits(&self) -> usize {
    self.0.len()
  }

  pub fn generator(&self) -> C::G {
    self.0[0]
  }
}

fn incomplete_addition<C: Ecip>(
  a: C::G,
  b: C::G,
) -> (C::FieldElement, C::FieldElement, C::FieldElement, C::FieldElement, C::FieldElement) {
  let (x1, y1) = C::to_xy(a);
  let (x2, y2) = C::to_xy(b);

  let c = a + b;

  let (x3, y3) = C::to_xy(c);

  let slope = (y2 - y1) *
    Option::<C::FieldElement>::from((x2 - x1).invert())
      .expect("trying to add perform incomplete addition on points which share an x coordinate");

  let x2m1 = x2 - x1;
  let x3m1 = x3 - x1;

  (x3, y3, slope, x2m1, x3m1)
}

/// Perform operations over the curve embedded into the proof's curve.
pub trait EmbeddedCurveOperations: Ciphersuite {
  type Embedded: Ecip<FieldElement = Self::F>;

  /// Constrains a point to being on curve AND not being the identity.
  fn constrain_on_curve<T: Transcript>(
    circuit: &mut Circuit<T, Self>,
    x: VariableReference,
    y: VariableReference,
  ) -> OnCurvePoint;

  /// Performs addition between two points, where P1 != P2, P1 != -P2, and neither P1 nor P2 are
  /// identity.
  ///
  /// The only checks performed by this function are P1 != P2 and P1 != -P2. Neither point is
  /// checked to not be identity.

  // Curve Trees, Appendix A.[4, 5]
  // This uses 4 gates theoretically, 5 as implemented here, and 6 constraints
  fn incomplete_add<T: Transcript>(
    circuit: &mut Circuit<T, Self>,
    p1: OnCurvePoint,
    p2: OnCurvePoint,
  ) -> OnCurvePoint {
    let OnCurvePoint { x: x1, y: y1 } = p1;
    let OnCurvePoint { x: x2, y: y2 } = p2;

    let (x3, y3, slope, x2m1, x3m1) = if circuit.prover() {
      let x1 = circuit.unchecked_value(x1).unwrap();
      let y1 = circuit.unchecked_value(y1).unwrap();
      let a = Self::Embedded::from_xy(x1, y1);

      let x2 = circuit.unchecked_value(x2).unwrap();
      let y2 = circuit.unchecked_value(y2).unwrap();
      let b = Self::Embedded::from_xy(x2, y2);

      let (x3, y3, slope, x2m1, x3m1) = incomplete_addition::<Self::Embedded>(a, b);

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

  /// Performs addition between two points, where P1 != P2, P1 != -P2, and neither P1 nor P2 are
  /// identity.
  ///
  /// The only checks performed by this function are P1 != P2, P1 != -P2, and P2 != identity. P1
  /// is not checked to not be identity.

  // Curve Trees, Appendix A.[4, 5]
  // This uses 4 gates theoretically, 5 as implemented here, and 6 constraints
  fn incomplete_add_constant<T: Transcript>(
    circuit: &mut Circuit<T, Self>,
    p1: OnCurvePoint,
    p2: <Self::Embedded as Ciphersuite>::G,
  ) -> OnCurvePoint {
    assert!(!bool::from(p2.is_identity()));

    let OnCurvePoint { x: x1, y: y1 } = p1;
    let (x2, y2) = Self::Embedded::to_xy(p2);

    let (x3, y3, slope, x2m1, x3m1) = if circuit.prover() {
      let x1 = circuit.unchecked_value(x1).unwrap();
      let y1 = circuit.unchecked_value(y1).unwrap();
      let a = Self::Embedded::from_xy(x1, y1);

      let (x3, y3, slope, x2m1, x3m1) = incomplete_addition::<Self::Embedded>(a, p2);

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

    // Prove x2m1 is non-zero, meaning x2 != x1, enabling incomplete formulas
    assert_non_zero_gadget(circuit, x2m1);

    // Constrain x2m1 is correct
    let mut constraint = Constraint::new("x2m1");
    constraint.weight(x1, Self::F::ONE);
    // Safe since the non-zero gadget will use it in a product statement
    constraint.weight(circuit.variable_to_product(x2m1).unwrap(), Self::F::ONE);
    constraint.rhs_offset(x2);
    circuit.constrain(constraint);

    // A.4 (6)
    {
      let ((_, _, slope_x2m1), _) = circuit.product(slope, x2m1);
      // slope_x2m1 - (y2 - y1) == 0
      // slope_x2m1 - y2 + y1 == 0
      // slope_x2m1 + y1 == y2
      let mut constraint = Constraint::new("slope_x2m1");
      constraint.weight(slope_x2m1, Self::F::ONE);
      constraint.weight(y1, Self::F::ONE);
      constraint.rhs_offset(y2);
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
      // -x2 == x1 + x3 - slope_squared
      let mut constraint = Constraint::new("slope_squared");
      constraint.weight(slope_squared, -Self::F::ONE);
      constraint.weight(x3_prod, Self::F::ONE);
      constraint.weight(x1, Self::F::ONE);
      constraint.rhs_offset(-x2);
      circuit.constrain(constraint);
    }

    OnCurvePoint { x: x3, y: y3 }
  }

  // This uses a divisor to prove knowledge of a DLog with just 1.75 gates per point, plus a
  // constant 2 gates
  // This is more than twice as performant as incomplete addition and is closer to being complete
  // (only identity is unsupported)
  //
  // Ideally, it's 1.5 gates per point, plus a constant 3 (if an O(1) divisor-non-zero check is
  // implemented)
  //
  // TODO: The currently implemented vector commitment scheme, if used, multiplies the gate count
  // by 7 due to adding 2 gates per item (with 3 items per gate (left, right, output))
  // That means this uses 12.25 gates per point
  // If a zero-cost vector commitment scheme isn't implemented, this isn't worth it for proofs
  // which don't already incur the vector commitment scheme's overhead
  //
  // Gate count is notated GC

  // TODO: Can we impl a batch DLog PoK?
  fn dlog_pok<R: RngCore + CryptoRng, T: Transcript>(
    rng: &mut R,
    circuit: &mut Circuit<T, Self>,
    G: &DLogTable<Self::Embedded>,
    p: OnCurvePoint,
    dlog: Option<<Self::Embedded as Ciphersuite>::F>,
  ) {
    let (bits, Gs) = if circuit.prover() {
      {
        let (x, y) = Self::Embedded::to_xy(G.0[0] * dlog.unwrap());
        assert_eq!(circuit.unchecked_value(p.x).unwrap(), x);
        assert_eq!(circuit.unchecked_value(p.y).unwrap(), y);
      }

      let mut trits = scalar_to_trits::<Self::Embedded>(dlog.unwrap());
      while trits.len() < G.1 {
        trits.push(Trit::Zero);
      }
      assert_eq!(trits.len(), G.1);

      let mut bits = vec![];
      let mut Gs = vec![];
      for (i, trit) in trits.iter().enumerate() {
        // TODO: This is not constant time
        bits.push(Some(Choice::from(match trit {
          Trit::NegOne => 1,
          Trit::Zero => 0,
          Trit::One => 1,
        })));
        Gs.push(match trit {
          Trit::NegOne => -G.0[i],
          Trit::Zero => <Self::Embedded as Ciphersuite>::G::identity(),
          Trit::One => G.0[i],
        });
      }
      (bits, Some(Gs))
    } else {
      (vec![None; G.1], None)
    };

    let mut dlog = Vec::with_capacity(bits.len());
    for bit in bits {
      dlog.push(Bit::new_from_choice(circuit, bit));
    }

    // These yx len checks should be the correct formulas...
    let yx_coeffs = |points| if points <= 4 { None } else { Some((points / 2) - 2) };
    let x_coeffs = |points| points / 2;

    let points = G.1 + 1;

    // Create the divisor
    let (y_coefficient, yx_coefficients, x_coefficients, zero_coefficient) = if circuit.prover() {
      let mut Gs = Gs.unwrap();
      Gs.push(-Self::Embedded::from_xy(
        circuit.unchecked_value(p.x).unwrap(),
        circuit.unchecked_value(p.y).unwrap(),
      ));
      assert_eq!(Gs.len(), points);

      // Drop all Gs which are identity
      let without_identity =
        Gs.drain(..).filter(|G| !bool::from(G.is_identity())).collect::<Vec<_>>();
      drop(Gs);

      // TODO: Can we achieve a more efficient divisor representation via derivatives?
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

    // Make sure one of the x coefficients is 1, and therefore that this divisor isn't equal to 0
    //
    // This is a O(n) algorithm since the polynomial is of variable length, and the highest-order
    // term is the one with a coefficient of 1
    //
    // We can normalize so the lowest-order term has a coefficient of 1, yet it'd make some
    // divisors unrepresentable. Doing so would be worth it if said divisors are negligible
    // (divisors for when only two bits in the scalar were set)
    //
    // Alternatively, a distinct method for proving the divisor isn't identical to zero may be
    // viable
    //
    // TODO

    // GC: 0.5 per point
    let x_coeffs = x_coeffs(points);
    let x_coefficients = if let Some(mut x_coefficients) = x_coefficients {
      let mut res = x_coefficients.drain(..).map(Some).collect::<Vec<_>>();
      while res.len() < x_coeffs {
        res.push(Some(Self::F::ZERO));
      }
      res
    } else {
      vec![None; x_coeffs]
    };
    assert_eq!(x_coefficients.len(), x_coeffs);
    let x_coefficients_sub_one = set_with_constant(circuit, Self::F::ONE, &x_coefficients);
    drop(x_coefficients);

    // We need to select a challenge point for the divisor
    // This requires committing to the divisor, a ZK variable
    // We do this by creating a vector commitment for the divisor's variables
    // This commitment is then what's hashed for challenges
    // Creating the commitment, along with evaluating the divisor, requires its presence in gates

    // The x coefficients were already used in gates thanks to checking one of them was 1
    // Technically, the coefficients - 1 were, yet that's irrelevant to the commitment

    let mut transcript = x_coefficients_sub_one.clone();

    // Add the rest of the divisor into the circuit
    // GC: 0.25 per point
    let (y_coefficient, yx_coefficients, zero_coefficient) = {
      // First, create a serial representation of the divisor
      let mut serial_divisor = {
        let mut serial_divisor = vec![];

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

        serial_divisor.push(y_coefficient);
        serial_divisor.push(zero_coefficient);
        serial_divisor
      };

      // Next, add all of the vars in circuit
      let serial_divisor =
        serial_divisor.drain(..).map(|e| circuit.add_secret_input(e)).collect::<Vec<_>>();

      // Use each variable in a product to enable their usage in constraints
      let mut serial_divisor = {
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
      let zero_coefficient = serial_divisor.pop().unwrap();
      let y_coefficient = serial_divisor.pop().unwrap();
      let yx_coefficients = serial_divisor;

      transcript.extend(&yx_coefficients);
      transcript.push(y_coefficient);
      transcript.push(zero_coefficient);

      (y_coefficient, yx_coefficients, zero_coefficient)
    };

    // Also transcript the DLog
    for bit in &dlog {
      // Note: We can only bind a single element, the re-composition of the DLog, if desirable
      // It'd be a single sharable gate and one constraint
      transcript.push(circuit.variable_to_product(bit.variable).unwrap());
    }

    // And finally the point itself
    transcript.push(circuit.variable_to_product(p.x).unwrap());
    transcript.push(circuit.variable_to_product(p.y).unwrap());

    // Create the commitment
    let commitment = circuit.allocate_vector_commitment();
    circuit.bind(commitment, transcript, None);
    let commitment = circuit
      .finalize_commitment(commitment, Some(Self::F::random(rng)).filter(|_| circuit.prover()));

    let challenge = Self::Embedded::hash_to_G("bp+_ecip", commitment.to_bytes().as_ref());

    // Evaluate the divisor over the challenge, and over -challenge
    let (challenge_x, challenge_y) = Self::Embedded::to_xy(challenge);

    // Create the powers of x
    assert!(x_coeffs > yx_coeffs(points).unwrap());
    let mut x_pows = vec![challenge_x];
    while x_pows.len() < x_coeffs {
      x_pows.push(*x_pows.last().unwrap() * challenge_x);
    }

    let mut lhs_constraint = Constraint::new("ecip_lhs");
    lhs_constraint.weight(zero_coefficient, Self::F::ONE);

    // Perform the x_coeffs
    let mut x_res = vec![];
    for i in 0 .. x_coeffs {
      // Because these x coefficients are minus 1, the left hand side will be short 1 x_pows[i]
      lhs_constraint.weight(x_coefficients_sub_one[i], x_pows[i]);
      // Adjust the right hand side accordingly
      lhs_constraint.rhs_offset(-x_pows[i]);

      x_res.push(
        circuit
          .unchecked_value(circuit.variable(x_coefficients_sub_one[i]))
          .map(|coeff_minus_one| (coeff_minus_one + Self::F::ONE) * x_pows[i]),
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

    // GC: 1 per point
    let mut accum = None;
    for (bit, G) in dlog.iter().zip(G.0.iter()).take(points - 1) {
      let this_rhs =
        bit.select_constant(circuit, Self::F::ONE, challenge_x - Self::Embedded::to_xy(*G).0);
      if let Some(accum_var) = accum {
        accum = Some(circuit.product(accum_var, this_rhs).1);
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
  fn constrain_on_curve<T: Transcript>(
    circuit: &mut Circuit<T, Self>,
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
