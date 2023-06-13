use rand_core::{RngCore, CryptoRng};

use subtle::{Choice, ConstantTimeEq, ConditionallySelectable};

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
  arithmetic_circuit::{Constraint, Circuit},
  gadgets::{Bit, set_membership::set_with_constant, elliptic_curve::*},
};

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
    let mut trits = scalar_to_trits::<C>(max);
    while trits.last().unwrap() == &Trit::Zero {
      trits.pop();
    }
    let trits = trits.len();

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
pub(crate) fn divisor_dlog_pok<
  R: RngCore + CryptoRng,
  T: Transcript,
  C: EmbeddedCurveOperations,
>(
  rng: &mut R,
  circuit: &mut Circuit<T, C>,
  G: &DLogTable<C::Embedded>,
  p: OnCurvePoint,
  dlog: Option<<C::Embedded as Ciphersuite>::F>,
) {
  let (bits, Gs) = if circuit.prover() {
    {
      let (x, y) = C::Embedded::to_xy(G.0[0] * dlog.unwrap());
      assert_eq!(circuit.unchecked_value(p.x), x);
      assert_eq!(circuit.unchecked_value(p.y), y);
    }

    let mut trits = scalar_to_trits::<C::Embedded>(dlog.unwrap());

    // TODO: This block is not const time
    {
      trits.truncate(G.1);
      while trits.len() < G.1 {
        trits.push(Trit::Zero);
      }
      assert_eq!(trits.len(), G.1);
    }

    let mut bits = vec![];
    let mut Gs = vec![];
    for (i, trit) in trits.iter().enumerate() {
      bits.push(Some(Choice::from(u8::conditional_select(&1, &0, trit.ct_eq(&Trit::Zero)))));
      let G = <C::Embedded as Ciphersuite>::G::conditional_select(
        &G.0[i],
        &<C::Embedded as Ciphersuite>::G::identity(),
        trit.ct_eq(&Trit::Zero),
      );
      Gs.push(<C::Embedded as Ciphersuite>::G::conditional_select(
        &G,
        &-G,
        trit.ct_eq(&Trit::NegOne),
      ));
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
    Gs.push(-C::Embedded::from_xy(circuit.unchecked_value(p.x), circuit.unchecked_value(p.y)));
    assert_eq!(Gs.len(), points);

    // Drop all Gs which are identity
    let without_identity =
      Gs.drain(..).filter(|G| !bool::from(G.is_identity())).collect::<Vec<_>>();
    drop(Gs);

    // TODO: Can we achieve a more efficient divisor representation via derivatives?
    let divisor = Divisor::<C::Embedded>::new(&without_identity);
    let Poly { y_coefficients, yx_coefficients, x_coefficients, zero_coefficient } = divisor;
    assert!(y_coefficients.len() <= 1);
    assert_eq!(yx_coeffs(without_identity.len()), yx_coefficients.get(0).map(|vec| vec.len()));
    assert_eq!(x_coeffs(without_identity.len()), x_coefficients.len());
    assert_eq!(x_coefficients.last().unwrap(), &C::F::ONE);

    (
      Some(y_coefficients.get(0).copied().unwrap_or(C::F::ZERO)),
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
      res.push(Some(C::F::ZERO));
    }
    res
  } else {
    vec![None; x_coeffs]
  };
  assert_eq!(x_coefficients.len(), x_coeffs);
  let x_coefficients_sub_one = set_with_constant(circuit, C::F::ONE, &x_coefficients);
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

      for i in 0 .. yx_coeffs(points).expect("only 2**4 points were allowed for this composition?")
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
              .unwrap_or(C::F::ZERO),
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
  let commitment =
    circuit.finalize_commitment(commitment, Some(C::F::random(rng)).filter(|_| circuit.prover()));

  let challenge = C::Embedded::hash_to_G("bp+_ecip", commitment.to_bytes().as_ref());

  // Evaluate the divisor over the challenge, and over -challenge
  let (challenge_x, challenge_y) = C::Embedded::to_xy(challenge);

  // Create the powers of x
  assert!(x_coeffs > yx_coeffs(points).unwrap());
  let mut x_pows = vec![challenge_x];
  while x_pows.len() < x_coeffs {
    x_pows.push(*x_pows.last().unwrap() * challenge_x);
  }

  let mut lhs_constraint = Constraint::new("ecip_lhs");
  lhs_constraint.weight(zero_coefficient, C::F::ONE);

  // Perform the x_coeffs
  let mut x_res = vec![];
  for i in 0 .. x_coeffs {
    // Because these x coefficients are minus 1, the left hand side will be short 1 x_pows[i]
    lhs_constraint.weight(x_coefficients_sub_one[i], x_pows[i]);
    // Adjust the right hand side accordingly
    lhs_constraint.rhs_offset(-x_pows[i]);

    x_res.push(if circuit.prover() {
      Some(
        (circuit.unchecked_value(circuit.variable(x_coefficients_sub_one[i])) + C::F::ONE) *
          x_pows[i],
      )
    } else {
      None
    });
  }

  // Perform the yx_coeffs
  let mut neg_lhs_constraint = lhs_constraint.clone();
  let mut yx_res = vec![];
  for i in 0 .. yx_coeffs(points).unwrap() {
    let yx = challenge_y * x_pows[i];
    lhs_constraint.weight(yx_coefficients[i], yx);
    neg_lhs_constraint.weight(yx_coefficients[i], -yx);
    yx_res.push(if circuit.prover() {
      Some(yx * circuit.unchecked_value(circuit.variable(yx_coefficients[i])))
    } else {
      None
    });
  }

  lhs_constraint.weight(y_coefficient, challenge_y);
  neg_lhs_constraint.weight(y_coefficient, -challenge_y);

  let (lhs, neg_lhs) = if circuit.prover() {
    let common = circuit.unchecked_value(circuit.variable(zero_coefficient)) +
      x_res.drain(..).map(Option::unwrap).sum::<C::F>();
    let yx = yx_res.drain(..).map(Option::unwrap).sum::<C::F>();
    let y = circuit.unchecked_value(circuit.variable(y_coefficient)) * challenge_y;
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
  lhs_constraint.weight(lhs_to_constrain, -C::F::ONE);
  circuit.constrain(lhs_constraint);
  neg_lhs_constraint.weight(neg_lhs_to_constrain, -C::F::ONE);
  circuit.constrain(neg_lhs_constraint);

  // Perform the right hand side evaluation

  // Iterate over the generators' forms, either including them or using the multiplicative
  // identity if that bit wasn't set

  // GC: 1 per point
  let mut accum = None;
  for (bit, G) in dlog.iter().zip(G.0.iter()).take(points - 1) {
    let this_rhs = bit.select_constant(circuit, C::F::ONE, challenge_x - C::Embedded::to_xy(*G).0);
    if let Some(accum_var) = accum {
      accum = Some(circuit.product(accum_var, this_rhs).1);
    } else {
      accum = Some(this_rhs);
    }
  }

  // Include the point the prover is claiming to know the DLog for
  let challenge_x_sub_x = circuit.add_secret_input(if circuit.prover() {
    Some(challenge_x - circuit.unchecked_value(p.x))
  } else {
    None
  });
  // GC: 1
  let ((_, challenge_x_sub_x, rhs), _) = circuit.product(accum.unwrap(), challenge_x_sub_x);
  let mut constraint = Constraint::new("challenge_x_sub_x");
  constraint.weight(
    circuit.variable_to_product(p.x).expect("point used in DLog PoK wasn't checked to be on curve"),
    C::F::ONE,
  );
  constraint.weight(challenge_x_sub_x, C::F::ONE);
  constraint.rhs_offset(challenge_x);
  circuit.constrain(constraint);

  circuit.constrain_equality(lhs, rhs);
}
