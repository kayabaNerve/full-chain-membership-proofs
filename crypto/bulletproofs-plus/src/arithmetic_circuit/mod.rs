use std::collections::{HashSet, HashMap};

use zeroize::{Zeroize, ZeroizeOnDrop};
use rand_core::{RngCore, CryptoRng};

use transcript::Transcript;

use multiexp::{multiexp, Point as MultiexpPoint, BatchVerifier};
use ciphersuite::{
  group::{ff::Field, Group, GroupEncoding},
  Ciphersuite,
};

use crate::{
  ScalarVector, PointVector, GeneratorsList, ProofGenerators, InnerProductGenerators,
  arithmetic_circuit_proof,
};
pub use arithmetic_circuit_proof::*;

mod challenge;
pub(crate) use challenge::*;

mod constraints;
use constraints::*;
pub use constraints::Constraint;

/// Blinded commitment to some variable.
#[allow(non_snake_case)]
#[derive(Clone, PartialEq, Eq, Debug, Zeroize, ZeroizeOnDrop)]
pub struct Commitment<C: Ciphersuite> {
  pub value: C::F,
  pub mask: C::F,
}

impl<C: Ciphersuite> Commitment<C> {
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
  pub fn calculate(&self, g: C::G, h: C::G) -> C::G {
    (g * self.value) + (h * self.mask)
  }
}

#[derive(Clone, Debug, Zeroize, ZeroizeOnDrop)]
enum Variable<C: Ciphersuite> {
  Secret(Option<C::F>),
  Committed(Option<Commitment<C>>),
  Product(usize, Option<C::F>),
}
/// A reference to a variable (some value), each usage guaranteed to be equivalent to all others.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Hash, Debug, Zeroize)]
pub struct VariableReference(usize);

/// A reference to a specific term in a product statement.
// Product is the product index it itself has, variable is the variable for each term.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Hash, Debug, Zeroize)]
pub enum ProductReference {
  Left { product: usize, variable: VariableReference },
  Right { product: usize, variable: VariableReference },
  Output { product: usize, variable: VariableReference },
}
impl ProductReference {
  fn id(&self) -> usize {
    match self {
      ProductReference::Left { product, .. } => *product,
      ProductReference::Right { product, .. } => *product,
      ProductReference::Output { product, .. } => *product,
    }
  }
  pub fn variable(&self) -> VariableReference {
    match self {
      ProductReference::Left { variable, .. } => *variable,
      ProductReference::Right { variable, .. } => *variable,
      ProductReference::Output { variable, .. } => *variable,
    }
  }
}

#[derive(Copy, Clone, Debug, Zeroize)]
pub struct CommitmentReference(usize);
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug, Zeroize)]
pub struct VectorCommitmentReference(usize);
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug, Zeroize)]
pub struct ChallengeReference(usize);
#[derive(Copy, Clone, PartialEq, Eq, Debug, Zeroize)]
pub struct PostValueReference(usize);

impl<C: Ciphersuite> Variable<C> {
  pub fn value(&self) -> Option<C::F> {
    match self {
      Variable::Secret(value) => *value,
      // This branch should never be reachable due to usage of CommitmentReference
      Variable::Committed(_commitment) => {
        // commitment.map(|commitment| commitment.value),
        panic!("requested value of commitment");
      }
      Variable::Product(_, product) => *product,
    }
  }
}

#[derive(Clone, PartialEq, Eq, Debug, Zeroize)]
struct Product {
  left: VariableReference,
  right: VariableReference,
  variable: VariableReference,
}

pub struct Circuit<'a, T: 'static + Transcript, C: Ciphersuite> {
  generators: ProofGenerators<'a, T, C>,

  prover: bool,

  commitments: usize,
  variables: Vec<Variable<C>>,

  products: Vec<Product>,
  vector_commitments: Vec<Vec<Option<C::F>>>,
  vector_commitment_blinds: Vec<Option<C::F>>,
  challenged_commitments: HashMap<VectorCommitmentReference, Option<C::G>>,
  challengers: HashMap<ChallengeReference, Box<dyn Challenger<T, C>>>,

  constraints: Vec<Constraint<C>>,
  variable_constraints: HashMap<VariableReference, Option<Constraint<C>>>,
  post_constraints: Vec<(Constraint<C>, Option<C::F>)>,
}

impl<'a, T: 'static + Transcript, C: Ciphersuite> Circuit<'a, T, C> {
  pub fn new(generators: ProofGenerators<'a, T, C>, prover: bool) -> Self {
    Self {
      generators,

      prover,

      commitments: 0,
      variables: vec![],

      products: vec![],
      vector_commitments: vec![],
      vector_commitment_blinds: vec![],
      challenged_commitments: HashMap::new(),
      challengers: HashMap::new(),

      constraints: vec![],
      variable_constraints: HashMap::new(),
      post_constraints: vec![],
    }
  }

  pub fn prover(&self) -> bool {
    self.prover
  }

  // TODO: Move to MultiexpPoint
  pub fn h(&self) -> C::G {
    self.generators.h().point()
  }

  /// Obtain the underlying value from a variable reference.
  ///
  /// Panics if not prover.
  pub fn unchecked_value(&self, variable: VariableReference) -> C::F {
    assert!(self.prover(), "verifier called for the unchecked_value");
    self.variables[variable.0].value().expect("prover didn't have a variable's value")
  }

  pub fn variable_to_product(&self, variable: VariableReference) -> Option<ProductReference> {
    if let Variable::Product(product, _) = self.variables[variable.0] {
      return Some(ProductReference::Output { product, variable });
    }

    for (product_id, product) in self.products.iter().enumerate() {
      let Product { left: l, right: r, variable: this_variable } = product;

      if !((variable == *l) || (variable == *r)) {
        continue;
      }

      if let Variable::Product(var_product_id, _) = self.variables[this_variable.0] {
        debug_assert_eq!(var_product_id, product_id);
        if variable == *l {
          return Some(ProductReference::Left {
            product: product_id,
            variable: self.products[var_product_id].left,
          });
        } else {
          return Some(ProductReference::Right {
            product: product_id,
            variable: self.products[var_product_id].right,
          });
        }
      } else {
        panic!("product pointed to non-product variable");
      }
    }

    None
  }

  /// Use a pair of variables in a product relationship.
  pub fn product(
    &mut self,
    a: VariableReference,
    b: VariableReference,
  ) -> ((ProductReference, ProductReference, ProductReference), VariableReference) {
    for (id, product) in self.products.iter().enumerate() {
      if (a == product.left) && (b == product.right) {
        return (
          (
            ProductReference::Left { product: id, variable: a },
            ProductReference::Right { product: id, variable: b },
            ProductReference::Output { product: id, variable: product.variable },
          ),
          product.variable,
        );
      }
    }

    let existing_a_use = self.variable_to_product(a);
    let existing_b_use = self.variable_to_product(b);

    let left = &self.variables[a.0];
    let right = &self.variables[b.0];

    let product_id = self.products.len();
    let variable = VariableReference(self.variables.len());
    let products = (
      ProductReference::Left { product: product_id, variable: a },
      ProductReference::Right { product: product_id, variable: b },
      ProductReference::Output { product: product_id, variable },
    );

    self.products.push(Product { left: a, right: b, variable });
    self.variables.push(Variable::Product(
      product_id,
      Some(()).filter(|_| self.prover).map(|_| left.value().unwrap() * right.value().unwrap()),
    ));

    // Add consistency constraints with prior variable uses
    // Or if this is the variables first usage, check if it has a constraint for said usage
    // The consistency constraint is prioritized as it's presumably cheaper
    if let Some(existing) = existing_a_use {
      self.constrain_equality(products.0, existing);
    } else if let Some(Some(mut constraint)) =
      self.variable_constraints.get_mut(&a).map(|constraint| constraint.take())
    {
      constraint.weight(products.0, -C::F::ONE);
      self.constrain(constraint);
    }
    if let Some(existing) = existing_b_use {
      self.constrain_equality(products.1, existing);
    } else if let Some(Some(mut constraint)) =
      self.variable_constraints.get_mut(&b).map(|constraint| constraint.take())
    {
      constraint.weight(products.1, -C::F::ONE);
      self.constrain(constraint);
    }

    // Insert that no constraint was used so we error if a variable constraint is later added
    self.variable_constraints.insert(a, None);
    self.variable_constraints.insert(b, None);

    (products, variable)
  }

  /// Add an input only known to the prover.
  pub fn add_secret_input(&mut self, value: Option<C::F>) -> VariableReference {
    assert_eq!(self.prover, value.is_some());

    let res = VariableReference(self.variables.len());
    self.variables.push(Variable::Secret(value));
    res
  }

  /// Add an input publicly committed to.
  pub fn add_committed_input(&mut self, commitment: Option<Commitment<C>>) -> CommitmentReference {
    assert_eq!(self.prover, commitment.is_some());

    let res = CommitmentReference(self.commitments);
    self.commitments += 1;
    self.variables.push(Variable::Committed(commitment));
    res
  }

  /// Allocate a vector commitment ID.
  pub fn allocate_vector_commitment(&mut self) -> VectorCommitmentReference {
    let res = VectorCommitmentReference(self.vector_commitments.len());
    self.vector_commitments.push(vec![]);
    // TODO: Don't use OsRng here, take in a RNG argument
    self
      .vector_commitment_blinds
      .push(Some(C::F::random(&mut rand_core::OsRng)).filter(|_| self.prover));
    res
  }

  // Add a variable into a vector commitment.
  pub fn add_to_vector_commitment(
    &mut self,
    commitment: VectorCommitmentReference,
    value: Option<C::F>,
  ) -> usize {
    assert_eq!(self.prover, value.is_some());
    assert!(
      !self.challenged_commitments.contains_key(&commitment),
      "commitment was already challenged"
    );

    let res = self.vector_commitments[commitment.0].len();
    self.vector_commitments[commitment.0].push(value);
    res
  }

  /// Add a constraint.
  ///
  /// Constraints are not transcripted. They are expected to be deterministic from the static
  /// program and higher-level statement. If your constraints are variable with regards to
  /// variables which aren't the commitments, transcript as needed before calling prove/verify.
  pub fn constrain(&mut self, constraint: Constraint<C>) {
    self.constraints.push(constraint);
  }

  /// Set a constraint to be applied to this variable once it's used in a product statement.
  pub fn set_variable_constraint(
    &mut self,
    variable: VariableReference,
    constraint: Constraint<C>,
  ) {
    assert!(self.variable_constraints.insert(variable, Some(constraint)).is_none());
  }

  pub fn constrain_equality(&mut self, a: ProductReference, b: ProductReference) {
    assert!(a != b);

    let mut constraint = Constraint::new("equality");
    constraint.weight(a, C::F::ONE);
    constraint.weight(b, -C::F::ONE);
    self.constrain(constraint);
  }

  pub fn post_constrain_equality(&mut self, a: ProductReference) -> PostValueReference {
    let res = PostValueReference(self.post_constraints.len());
    let mut constraint = Constraint::new("post-equality");
    constraint.weight(a, C::F::ONE);
    self.post_constraints.push((
      constraint,
      if self.prover { Some(self.unchecked_value(a.variable())) } else { None },
    ));
    res
  }

  pub fn equals_constant(&mut self, a: ProductReference, b: C::F) {
    let mut constraint = Constraint::new("constant_equality");
    if b == C::F::ZERO {
      constraint.weight(a, C::F::ONE);
    } else {
      constraint.weight(a, b.invert().unwrap());
      constraint.rhs_offset(C::F::ONE);
    }
    self.constrain(constraint);
  }

  /// Obtain a challenge usable mid-circuit via hashing a commitment to some subset of variables.
  ///
  /// Takes in a challenger which maps a T::Challenge to a series of C::F challenges.
  pub fn in_circuit_challenge(
    &mut self,
    commitment: VectorCommitmentReference,
    challenger: Box<dyn Challenger<T, C>>,
  ) -> (ChallengeReference, Option<Vec<C::F>>) {
    let challenge_ref = ChallengeReference(commitment.0);
    let res = if self.prover() {
      let mut C = C::G::identity();
      for (i, value) in self.vector_commitments[commitment.0].iter().enumerate() {
        C += self.generators.generator(GeneratorsList::GBold1, i).point() * value.unwrap();
      }
      C += self.generators.h().point() * self.vector_commitment_blinds[commitment.0].unwrap();
      assert!(
        self.challenged_commitments.insert(commitment, Some(C)).is_none(),
        "commitment was already challenged"
      );

      (challenge_ref, Some(challenger(commitment_challenge::<T, C>(C))))
    } else {
      assert!(
        self.challenged_commitments.insert(commitment, None).is_none(),
        "commitment was already challenged"
      );
      (challenge_ref, None)
    };
    assert!(
      self.challengers.insert(challenge_ref, challenger).is_none(),
      "challenger already defined for this vector commitment"
    );
    res
  }

  fn compile(
    self,
  ) -> (
    ProofGenerators<'a, T, C>,
    Option<Vec<C::G>>,
    Vec<Option<C::F>>,
    Option<Vec<C::G>>,
    HashMap<ChallengeReference, Box<dyn Challenger<T, C>>>,
    Weights<C>,
    Vec<C::F>,
    Option<ArithmeticCircuitWitness<C>>,
  ) {
    // Ensure all variable constraints ended up used
    for variable_constraint in self.variable_constraints.values() {
      assert!(variable_constraint.is_none());
    }

    let (commitments, C, C_values, c_gamma, witness) = if self.prover {
      let mut aL = vec![];
      let mut aR = vec![];

      let mut commitments = vec![];
      let mut v = vec![];
      let mut gamma = vec![];

      let mut C = vec![];
      let mut C_values = vec![];

      for variable in &self.variables {
        match variable {
          Variable::Secret(_) => {}
          Variable::Committed(value) => {
            let value = value.as_ref().unwrap();
            commitments
              .push(value.calculate(self.generators.g().point(), self.generators.h().point()));
            v.push(value.value);
            gamma.push(value.mask);
          }
          Variable::Product(product_id, _) => {
            let product = &self.products[*product_id];
            aL.push(self.variables[product.left.0].value().unwrap());
            aR.push(self.variables[product.right.0].value().unwrap());
          }
        }
      }

      for (i, vector_commitment) in self.vector_commitments.iter().enumerate() {
        C.push(if let Some(C) = self.challenged_commitments.get(&VectorCommitmentReference(i)) {
          C_values.push(ScalarVector(vec![]));
          for value in vector_commitment {
            C_values[i].0.push(value.unwrap());
          }
          C.unwrap()
        } else {
          let mut this_C = C::G::identity();
          C_values.push(ScalarVector(vec![]));
          for (j, value) in vector_commitment.iter().enumerate() {
            this_C += self.generators.generator(GeneratorsList::GBold1, j).point() * value.unwrap();
            C_values[i].0.push(value.unwrap());
          }
          this_C += self.generators.h().point() * self.vector_commitment_blinds[i].unwrap();
          this_C
        });
      }

      (
        Some(commitments),
        Some(C),
        Some(C_values.clone()),
        Some(self.vector_commitment_blinds.clone()),
        Some(ArithmeticCircuitWitness::new(
          ScalarVector(aL),
          ScalarVector(aR),
          ScalarVector(v),
          ScalarVector(gamma),
          C_values,
          self.vector_commitment_blinds.iter().map(|s| s.unwrap()).collect(),
        )),
      )
    } else {
      (None, None, None, None, None)
    };

    let mut V_len = 0;
    let mut n = 0;
    for variable in &self.variables {
      match variable {
        Variable::Secret(_) => {}
        Variable::Committed(_) => V_len += 1,
        Variable::Product(_, _) => n += 1,
      }
    }
    assert_eq!(self.commitments, V_len);

    let mut C_len = self.vector_commitment_blinds.len();
    let mut vector_commitments = C_values;

    // Check the constraints are well-formed
    if self.prover() {
      for constraint in &self.constraints {
        if !(constraint.challenge_weights.is_empty() && constraint.c_challenge.is_none()) {
          continue;
        }

        // WL aL WR aR WO aO == WV v + c
        let mut eval = C::F::ZERO;
        for wl in &constraint.WL {
          eval += wl.1 * witness.as_ref().unwrap().aL[wl.0];
        }
        for wr in &constraint.WR {
          eval += wr.1 * witness.as_ref().unwrap().aR[wr.0];
        }
        for wo in &constraint.WO {
          eval += wo.1 * (witness.as_ref().unwrap().aL[wo.0] * witness.as_ref().unwrap().aR[wo.0]);
        }
        for ((i, c), weight) in constraint.WC.iter() {
          eval += *weight * witness.as_ref().unwrap().c[*i][*c];
        }
        for wv in &constraint.WV {
          eval -= wv.1 * witness.as_ref().unwrap().v[wv.0];
        }

        assert_eq!(eval, constraint.c, "faulty constraint: {}", constraint.label);
      }
    }

    let mut post_constraints = Vec::with_capacity(self.post_constraints.len());
    let mut post_values = Vec::with_capacity(self.post_constraints.len());
    for post_constraint in self.post_constraints {
      post_constraints.push(post_constraint.0);
      if let Some(value) = post_constraint.1 {
        post_values.push(value);
      }
    }
    let weights = Weights::new(n, V_len, C_len, self.constraints, post_constraints);

    (
      self.generators,
      commitments,
      self.vector_commitment_blinds,
      C,
      self.challengers,
      weights,
      post_values,
      witness,
    )
  }

  // Returns the commitments, the vector commitment blinds used, the blinded vector commitments,
  // and the proof
  // TODO: Create a dedicated struct for this return value
  pub fn prove<R: RngCore + CryptoRng>(
    self,
    rng: &mut R,
    transcript: &mut T,
  ) -> (Vec<C::G>, Vec<C::F>, Vec<C::G>, ArithmeticCircuitProof<C>) {
    assert!(self.prover);

    let C_len = self.vector_commitment_blinds.len();

    let (
      proof_generators,
      V,
      vector_commitment_blinds,
      C,
      challengers,
      weights,
      post_values,
      witness,
    ) = self.compile();
    let witness = witness.unwrap();

    let mut challenges = vec![vec![]; C_len];
    for (challenge, challenger) in challengers {
      challenges[challenge.0] =
        challenger(commitment_challenge::<T, C>(C.as_ref().unwrap()[challenge.0]));
    }

    let weights = weights.build(post_values, &challenges);
    let proof = ArithmeticCircuitStatement::new(
      proof_generators,
      PointVector(V.clone().unwrap()),
      PointVector(C.clone().unwrap()),
      weights.0,
      weights.1,
      weights.2,
      weights.3,
      weights.4,
      weights.5,
    )
    .prove(rng, transcript, witness);

    (
      V.unwrap(),
      vector_commitment_blinds.into_iter().map(|vc| vc.unwrap()).collect(),
      C.unwrap(),
      proof,
    )
  }

  pub fn verification_statement(self) -> ArithmeticCircuit<'a, T, C> {
    assert!(!self.prover);
    let (proof_generators, _, _, _, challengers, weights, _, _) = self.compile();

    ArithmeticCircuit { proof_generators, challengers, weights }
  }
}

pub struct ArithmeticCircuit<'a, T: 'static + Transcript, C: Ciphersuite> {
  proof_generators: ProofGenerators<'a, T, C>,
  challengers: HashMap<ChallengeReference, Box<dyn Challenger<T, C>>>,
  weights: Weights<C>,
}

impl<'a, T: 'static + Transcript, C: Ciphersuite> ArithmeticCircuit<'a, T, C> {
  pub fn verify<R: RngCore + CryptoRng>(
    &self,
    rng: &mut R,
    verifier: &mut BatchVerifier<(), C::G>,
    transcript: &mut T,
    commitments: Vec<C::G>,
    vector_commitments: Vec<C::G>,
    post_values: Vec<C::F>,
    proof: ArithmeticCircuitProof<C>,
  ) {
    let mut challenges = vec![vec![]; vector_commitments.len()];
    for (challenge, challenger) in &self.challengers {
      challenges[challenge.0] =
        challenger(commitment_challenge::<T, C>(vector_commitments[challenge.0]));
    }

    let weights = self.weights.build(post_values, &challenges);
    ArithmeticCircuitStatement::new(
      self.proof_generators.clone(),
      PointVector(commitments),
      PointVector(vector_commitments),
      weights.0,
      weights.1,
      weights.2,
      weights.3,
      weights.4,
      weights.5,
    )
    .verify(rng, verifier, transcript, proof);
  }
}
