use std::collections::HashMap;

use rand_core::{RngCore, CryptoRng};

use zeroize::{Zeroize, ZeroizeOnDrop};

use transcript::Transcript;

use ciphersuite::group::ff::Field;

#[rustfmt::skip]
use crate::{BulletproofsCurve, ScalarVector, ScalarMatrix, PointVector, arithmetic_circuit_proof::*};

#[allow(non_snake_case)]
#[derive(Clone, PartialEq, Eq, Debug, Zeroize, ZeroizeOnDrop)]
pub struct Commitment<C: BulletproofsCurve> {
  pub value: C::F,
  pub mask: C::F,
}

impl<C: BulletproofsCurve> Commitment<C> {
  pub fn zero() -> Self {
    Commitment { value: C::F::ZERO, mask: C::F::ZERO }
  }

  pub fn new(value: C::F, mask: C::F) -> Self {
    Commitment { value, mask }
  }

  pub fn masking<R: RngCore + CryptoRng>(rng: &mut R, value: C::F) -> Self {
    Commitment { value, mask: C::F::random(rng) }
  }

  /// Calculate a Pedersen commitment, as a point, from the transparent structure.
  pub fn calculate(&self) -> C::G {
    (C::generator() * self.value) + (C::alt_generator() * self.mask)
  }
}

#[derive(Clone, Debug)]
pub struct Constraint<C: BulletproofsCurve> {
  label: &'static str,
  // Each weight (C::F) is bound to a specific variable (usize) to allow post-expansion to valid
  // constraints
  WL: Vec<(usize, C::F)>,
  WR: Vec<(usize, C::F)>,
  WO: Vec<(usize, C::F)>,
  WV: Vec<(usize, C::F)>,
  c: C::F,
}

impl<C: BulletproofsCurve> Constraint<C> {
  pub fn new(label: &'static str) -> Self {
    Self { label, WL: vec![], WR: vec![], WO: vec![], WV: vec![], c: C::F::ZERO }
  }

  pub fn weight(&mut self, product: ProductReference, weight: C::F) -> &mut Self {
    let (weights, id) = match product {
      ProductReference::Left(id, _) => (&mut self.WL, id),
      ProductReference::Right(id, _) => (&mut self.WR, id),
      ProductReference::Output(id, _) => (&mut self.WO, id),
    };
    for existing in &*weights {
      assert!(existing.0 != id);
    }
    weights.push((id, weight));
    self
  }
  pub fn weight_commitment(&mut self, variable: CommitmentReference, weight: C::F) -> &mut Self {
    for existing in &self.WV {
      assert!(existing.0 != variable.0);
    }
    self.WV.push((variable.0, weight));
    self
  }
  pub fn offset(&mut self, offset: C::F) -> &mut Self {
    assert!(bool::from(self.c.is_zero()));
    self.c = offset;
    self
  }
}

#[derive(Copy, Clone, Debug, Zeroize)]
pub struct VariableReference(usize);
#[derive(Copy, Clone, Debug, Zeroize)]
pub enum ProductReference {
  Left(usize, usize),
  Right(usize, usize),
  Output(usize, usize),
}
#[derive(Copy, Clone, Debug, Zeroize)]
pub struct CommitmentReference(usize);

#[derive(Clone, Debug, Zeroize, ZeroizeOnDrop)]
pub enum Variable<C: BulletproofsCurve> {
  Constant(C::F),
  Secret(Option<C::F>),
  Public(Option<Commitment<C>>, C::G),
  Product(usize, usize, Option<C::F>),
}

impl<C: BulletproofsCurve> Variable<C> {
  pub fn value(&self) -> Option<C::F> {
    match self {
      Variable::Constant(value) => Some(*value),
      Variable::Secret(value) => *value,
      // This branch should never be reachable due to usage of CommitmentReference
      Variable::Public(_commitment, _) => {
        // commitment.map(|commitment| commitment.value),
        panic!("requested value of commitment");
      }
      Variable::Product(_, _, product) => *product,
    }
  }
}

impl<C: BulletproofsCurve> core::ops::Add for Variable<C> {
  type Output = Option<C::F>;

  fn add(self, other: Variable<C>) -> Self::Output {
    if let (Some(a), Some(b)) = (self.value(), other.value()) {
      Some(a + b)
    } else {
      None
    }
  }
}

impl<C: BulletproofsCurve> core::ops::Sub for Variable<C> {
  type Output = Option<C::F>;

  fn sub(self, other: Variable<C>) -> Self::Output {
    if let (Some(a), Some(b)) = (self.value(), other.value()) {
      Some(a - b)
    } else {
      None
    }
  }
}

pub struct Circuit<C: BulletproofsCurve> {
  g_bold1: PointVector<C>,
  g_bold2: PointVector<C>,
  h_bold1: PointVector<C>,
  h_bold2: PointVector<C>,

  prover: bool,
  variables: Vec<Variable<C>>,
  commitments: usize,
  products: usize,
  constraints: Vec<Constraint<C>>,

  pending_additive_constraints: Vec<(Constraint<C>, VariableReference)>,
}

impl<C: BulletproofsCurve> Circuit<C> {
  pub fn new(
    g_bold1: PointVector<C>,
    g_bold2: PointVector<C>,
    h_bold1: PointVector<C>,
    h_bold2: PointVector<C>,
    prover: bool,
  ) -> Self {
    Self {
      g_bold1,
      g_bold2,
      h_bold1,
      h_bold2,

      prover,
      variables: vec![],
      commitments: 0,
      products: 0,
      constraints: vec![],

      pending_additive_constraints: vec![],
    }
  }

  pub fn prover(&self) -> bool {
    self.prover
  }

  pub fn add_constant(&mut self, constant: C::F) -> VariableReference {
    // Return the existing constant, if there's already one
    for (i, variable) in self.variables.iter().enumerate() {
      match variable {
        Variable::Constant(value) => {
          if *value == constant {
            return VariableReference(i);
          }
        }
        _ => {}
      }
    }

    let res = VariableReference(self.variables.len());
    self.variables.push(Variable::Constant(constant));
    let mut constraint = Constraint::new("constant");
    // Negative as pending_additive_constraints negates its contribution, expecting it to be
    // left-hand-side balanced, where this is right-hand-side balanced
    constraint.offset(-constant);
    self.pending_additive_constraints.push((constraint, res));
    res
  }

  /// Add an input only known to the prover.
  ///
  /// This value must be used in a product relationship in order to be used in constraints.
  pub fn add_secret_input(&mut self, value: Option<C::F>) -> VariableReference {
    assert_eq!(self.prover, value.is_some());

    let res = VariableReference(self.variables.len());
    self.variables.push(Variable::Secret(value));
    res
  }

  /// Add an input publicly committed to.
  pub fn add_committed_input(
    &mut self,
    commitment: Option<Commitment<C>>,
    actual: C::G,
  ) -> CommitmentReference {
    assert_eq!(self.prover, commitment.is_some());
    if let Some(commitment) = commitment.clone() {
      assert_eq!(commitment.calculate(), actual);
    }

    let res = CommitmentReference(self.commitments);
    self.commitments += 1;
    self.variables.push(Variable::Public(commitment, actual));
    res
  }

  /// Use a pair of variables in a product relationship.
  ///
  /// This is unsafe without further constraints on the variables/product.
  pub fn unchecked_product(
    &mut self,
    a: VariableReference,
    b: VariableReference,
  ) -> (ProductReference, ProductReference, ProductReference) {
    let left = &self.variables[a.0];
    let right = &self.variables[b.0];

    let product_id = self.products;
    let variable_id = self.variables.len();
    self.products += 1;
    self.variables.push(Variable::Product(
      a.0,
      b.0,
      left.value().and_then(|left| right.value().and_then(|right| Some(left * right))),
    ));
    (
      ProductReference::Left(product_id, variable_id),
      ProductReference::Right(product_id, variable_id),
      ProductReference::Output(product_id, variable_id),
    )
  }

  pub fn constrain_equality(&mut self, a: ProductReference, b: ProductReference) {
    let mut constraint = Constraint::new("equality");
    constraint.weight(a, C::F::ONE);
    constraint.weight(b, -C::F::ONE);
    self.constrain(constraint);
  }

  pub fn product(&mut self, a: ProductReference, b: ProductReference) -> ProductReference {
    let a_var = self.product_to_unchecked_variable(a);
    let b_var = self.product_to_unchecked_variable(b);
    let res = self.unchecked_product(a_var, b_var);
    self.constrain_equality(res.0, a);
    self.constrain_equality(res.1, b);
    res.2
  }

  /// Create, and constrain, a variable to be the sum of two other variables.
  ///
  /// All usages of this variable in product statements will be appropriately constrained.
  pub fn add(&mut self, a: ProductReference, b: ProductReference) -> VariableReference {
    let a_var = self.product_to_unchecked_variable(a);
    let b_var = self.product_to_unchecked_variable(b);
    let sum =
      self.add_secret_input(self.unchecked_variable(a_var) + self.unchecked_variable(b_var));
    let mut constraint = Constraint::new("addition");
    constraint.weight(a, C::F::ONE);
    constraint.weight(b, C::F::ONE);
    // We can only add a constraint for this once the sum has been used in a product statement
    // Add it as pending, so once the circuit uses it in one naturally, we can use that
    self.pending_additive_constraints.push((constraint, sum));
    sum
  }

  /// Obtain the underlying variable from a reference.
  ///
  /// This requires a constraint to be safely used.
  pub fn unchecked_variable(&self, variable: VariableReference) -> Variable<C> {
    self.variables[variable.0].clone()
  }

  /// Obtain a variable from a product.
  ///
  /// This returns the requested variable yet further requires a constraint of equality between the
  /// variables.
  pub fn product_to_unchecked_variable(&mut self, product: ProductReference) -> VariableReference {
    let variable = match product {
      ProductReference::Left(_, variable) => variable,
      ProductReference::Right(_, variable) => variable,
      ProductReference::Output(_, variable) => variable,
    };
    match self.variables[variable] {
      Variable::Product(left, right, output) => match product {
        ProductReference::Left(_, _) => VariableReference(left),
        ProductReference::Right(_, _) => VariableReference(right),
        ProductReference::Output(_, _) => self.add_secret_input(output),
      },
      _ => panic!("ProductReference to non-product"),
    }
  }

  /// Add a constraint.
  pub fn constrain(&mut self, constraint: Constraint<C>) {
    // TODO: Check commitment weights refer to commitments, W{L, R, O} refer to product terms
    self.constraints.push(constraint);
  }

  // TODO: This can be significantly optimized
  fn compile(mut self) -> (ArithmeticCircuitStatement<C>, Option<ArithmeticCircuitWitness<C>>) {
    // aL, aR, v, gamma
    let witness = if self.prover {
      let mut variables = HashMap::new();

      let mut aL = vec![];
      let mut aR = vec![];

      let mut v = vec![];
      let mut gamma = vec![];

      for (i, variable) in self.variables.iter().enumerate() {
        match variable {
          Variable::Constant(value) => {
            variables.insert(i, *value);
          }
          Variable::Secret(value) => {
            variables.insert(i, value.unwrap());
          }
          Variable::Public(value, actual) => {
            let value = value.as_ref().unwrap();
            assert_eq!(value.calculate(), *actual);
            v.push(value.value);
            gamma.push(value.mask);
          }
          Variable::Product(left, right, value) => {
            aL.push(variables[left]);
            aR.push(variables[right]);
            variables.insert(i, value.unwrap());
          }
        }
      }

      Some(ArithmeticCircuitWitness::new(
        ScalarVector(aL),
        ScalarVector(aR),
        ScalarVector(v),
        ScalarVector(gamma),
      ))
    } else {
      None
    };

    let mut V = vec![];
    let mut n = 0;
    for variable in &self.variables {
      match variable {
        Variable::Constant(_) => {}
        Variable::Secret(_) => {}
        Variable::Public(_, actual) => V.push(*actual),
        Variable::Product(_, _, _) => n += 1,
      }
    }

    for (constraint, sum) in self.pending_additive_constraints {
      // Look for a product using this variable
      let start = self.constraints.len();
      let mut i = 0;
      for (variable_id, product) in self.variables.iter().enumerate() {
        match product {
          Variable::Product(left, right, _) => {
            if *left == sum.0 {
              // TODO: If this is the second constraint, a more minimal constraint can be used
              // (1 prior, -1 current, instead of 1, 1, -1)
              let mut constraint = constraint.clone();
              constraint.weight(ProductReference::Left(i, variable_id), -C::F::ONE);
              self.constraints.push(constraint);
            }

            if *right == sum.0 {
              let mut constraint = constraint.clone();
              constraint.weight(ProductReference::Right(i, variable_id), -C::F::ONE);
              self.constraints.push(constraint);
            }

            i += 1;
          }
          _ => {}
        }
      }

      if start == self.constraints.len() {
        panic!("unused additive sum");
      }
    }

    // WL, WR, WO, WV, c
    let mut WL = vec![];
    let mut WR = vec![];
    let mut WO = vec![];
    let mut WV = vec![];
    let mut c = vec![];
    for constraint in self.constraints {
      // WL aL WR aR WO aO == WV v + c
      let mut eval = C::F::ZERO;

      let mut this_wl = vec![C::F::ZERO; n];
      let mut this_wr = vec![C::F::ZERO; n];
      let mut this_wo = vec![C::F::ZERO; n];
      let mut this_wv = vec![C::F::ZERO; V.len()];

      for wl in constraint.WL {
        if self.prover {
          eval += wl.1 * witness.as_ref().unwrap().aL[wl.0];
        }
        this_wl[wl.0] = wl.1;
      }
      for wr in constraint.WR {
        if self.prover {
          eval += wr.1 * witness.as_ref().unwrap().aR[wr.0];
        }
        this_wr[wr.0] = wr.1;
      }
      for wo in constraint.WO {
        if self.prover {
          eval += wo.1 * (witness.as_ref().unwrap().aL[wo.0] * witness.as_ref().unwrap().aR[wo.0]);
        }
        this_wo[wo.0] = wo.1;
      }
      for wv in constraint.WV {
        if self.prover {
          eval -= wv.1 * witness.as_ref().unwrap().v[wv.0];
        }
        this_wv[wv.0] = wv.1;
      }

      if self.prover {
        assert_eq!(eval, constraint.c, "faulty constraint: {}", constraint.label);
      }

      WL.push(ScalarVector(this_wl));
      WR.push(ScalarVector(this_wr));
      WO.push(ScalarVector(this_wo));
      WV.push(ScalarVector(this_wv));
      c.push(constraint.c);
    }

    (
      ArithmeticCircuitStatement::new(
        self.g_bold1,
        self.g_bold2,
        self.h_bold1,
        self.h_bold2,
        PointVector(V),
        ScalarMatrix(WL),
        ScalarMatrix(WR),
        ScalarMatrix(WO),
        ScalarMatrix(WV),
        ScalarVector(c),
      ),
      witness,
    )
  }

  pub fn prove<R: RngCore + CryptoRng, T: Transcript>(
    self,
    rng: &mut R,
    transcript: &mut T,
  ) -> ArithmeticCircuitProof<C> {
    assert!(self.prover);
    let (statement, witness) = self.compile();
    statement.prove(rng, transcript, witness.unwrap())
  }

  pub fn verify<T: Transcript>(self, transcript: &mut T, proof: ArithmeticCircuitProof<C>) {
    assert!(!self.prover);
    let (statement, _) = self.compile();
    statement.verify(transcript, proof)
  }
}
