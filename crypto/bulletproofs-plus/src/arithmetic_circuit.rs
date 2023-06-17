use std::collections::{HashSet, HashMap};

use zeroize::{Zeroize, ZeroizeOnDrop};
use rand_core::{RngCore, CryptoRng};

use transcript::Transcript;

use multiexp::{multiexp, Point as MultiexpPoint, BatchVerifier};
use ciphersuite::{
  group::{ff::Field, GroupEncoding},
  Ciphersuite,
};

use crate::{
  ScalarVector, ScalarMatrix, PointVector, VectorCommitmentGenerators, GeneratorsList,
  ProofGenerators, InnerProductGenerators, weighted_inner_product::*, arithmetic_circuit_proof,
};
pub use arithmetic_circuit_proof::*;

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
pub enum Variable<C: Ciphersuite> {
  Secret(Option<C::F>),
  Committed(Option<Commitment<C>>),
  Product(usize, Option<C::F>),
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug, Zeroize)]
pub struct VariableReference(usize);
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Hash, Debug, Zeroize)]
pub enum ProductReference {
  Left { product: usize, variable: usize },
  Right { product: usize, variable: usize },
  Output { product: usize, variable: usize },
}
#[derive(Copy, Clone, Debug, Zeroize)]
pub struct CommitmentReference(usize);
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug, Zeroize)]
pub struct VectorCommitmentReference(usize);
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug, Zeroize)]
pub struct ChallengeReference(usize);
#[derive(Copy, Clone, PartialEq, Eq, Debug, Zeroize)]
pub struct PostValueReference(usize);

mod sealed {
  use transcript::Transcript;
  use ciphersuite::Ciphersuite;

  pub trait Challenger<T: Transcript, C: Ciphersuite>: Fn(T::Challenge) -> Vec<C::F> {}
  impl<T: Transcript, C: Ciphersuite, F: Fn(T::Challenge) -> Vec<C::F>> Challenger<T, C> for F {}

  pub trait ChallengeApplicator<C: Ciphersuite>: Fn(&[C::F]) -> C::F {}
  impl<C: Ciphersuite, F: Fn(&[C::F]) -> C::F> ChallengeApplicator<C> for F {}
}
use sealed::*;

/// A constraint of the form WL aL + WR aR + WO aO = WV V + c.
pub struct Constraint<C: Ciphersuite> {
  label: &'static str,
  // Each weight (C::F) is bound to a specific ProductReference (usize) to allow post-expansion to
  // valid constraints
  WL: Vec<(usize, C::F)>,
  WR: Vec<(usize, C::F)>,
  WO: Vec<(usize, C::F)>,
  WV: Vec<(usize, C::F)>,
  challenge_weights:
    HashMap<ProductReference, (ChallengeReference, Box<dyn ChallengeApplicator<C>>)>,
  c: C::F,
  c_challenge: Option<(ChallengeReference, Box<dyn ChallengeApplicator<C>>)>,
}

impl<C: Ciphersuite> Clone for Constraint<C> {
  fn clone(&self) -> Self {
    assert!(self.challenge_weights.is_empty());
    assert!(self.c_challenge.is_none());
    Self {
      label: self.label,
      WL: self.WL.clone(),
      WR: self.WR.clone(),
      WO: self.WO.clone(),
      WV: self.WV.clone(),
      challenge_weights: HashMap::new(),
      c: self.c,
      c_challenge: None,
    }
  }
}

impl<C: Ciphersuite> core::fmt::Debug for Constraint<C> {
  fn fmt(&self, fmt: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
    fmt.debug_struct("Constraint").finish_non_exhaustive()
  }
}

impl<C: Ciphersuite> Constraint<C> {
  // Create a new Constraint with the specified label.
  pub fn new(label: &'static str) -> Self {
    Self {
      label,
      WL: vec![],
      WR: vec![],
      WO: vec![],
      WV: vec![],
      challenge_weights: HashMap::new(),
      c: C::F::ZERO,
      c_challenge: None,
    }
  }

  /// Cummulatively weight the specified product by the specified weight.
  pub fn weight(&mut self, product: ProductReference, weight: C::F) -> &mut Self {
    assert!(
      !self.challenge_weights.contains_key(&product),
      "weighted product already has a challenge weight"
    );

    let (weights, id) = match product {
      ProductReference::Left { product: id, variable: _ } => (&mut self.WL, id),
      ProductReference::Right { product: id, variable: _ } => (&mut self.WR, id),
      ProductReference::Output { product: id, variable: _ } => (&mut self.WO, id),
    };
    for existing in &mut *weights {
      if existing.0 == id {
        existing.1 += weight;
        return self;
      }
    }
    weights.push((id, weight));
    self
  }

  /// Weight a product by a challenge, mapped as the function specifies.
  ///
  /// Panics if the product already has a weight specified in this constraint.
  pub fn weight_with_challenge(
    &mut self,
    product: ProductReference,
    challenge: ChallengeReference,
    applicator: Box<dyn ChallengeApplicator<C>>,
  ) -> &mut Self {
    assert!(self.challenge_weights.insert(product, (challenge, applicator)).is_none());

    let (weights, id) = match product {
      ProductReference::Left { product: id, variable: _ } => (&self.WL, id),
      ProductReference::Right { product: id, variable: _ } => (&self.WR, id),
      ProductReference::Output { product: id, variable: _ } => (&self.WO, id),
    };
    for existing in weights {
      if existing.0 == id {
        panic!("product weighted by challenge already has a non-challenge weight");
      }
    }

    self
  }

  /// Cummulatively weight the specified commitment by the specified weight.
  pub fn weight_commitment(&mut self, variable: CommitmentReference, weight: C::F) -> &mut Self {
    for existing in &self.WV {
      assert!(existing.0 != variable.0);
    }
    self.WV.push((variable.0, weight));
    self
  }

  /// Add a value to the `c` variable on the right-hand side of the constraint statement.
  pub fn rhs_offset(&mut self, offset: C::F) -> &mut Self {
    assert!(self.c_challenge.is_none());
    self.c += offset;
    self
  }

  /// Add an applied challenge to the `c` variable on the right-hand side of the constraint
  /// statement.
  ///
  /// Panics if the rhs offset already has a weight specified in this constraint.
  pub fn rhs_offset_with_challenge(
    &mut self,
    challenge: ChallengeReference,
    applicator: Box<dyn ChallengeApplicator<C>>,
  ) -> &mut Self {
    assert!(bool::from(self.c.is_zero()));
    assert!(self.c_challenge.is_none());
    self.c_challenge = Some((challenge, applicator));
    self
  }
}

// TODO: Take in a transcript
fn commitment_challenge<T: Transcript, C: Ciphersuite>(commitment: C::G) -> T::Challenge {
  let mut transcript = T::new(b"Bulletproofs+ Commitment Challenge");
  transcript.append_message(b"commitment", commitment.to_bytes());
  transcript.challenge(b"challenge")
}

fn embed_challenges<C: Ciphersuite>(
  WL: &mut Vec<(usize, C::F)>,
  WR: &mut Vec<(usize, C::F)>,
  WO: &mut Vec<(usize, C::F)>,
  challenge_weights: &HashMap<
    ProductReference,
    (ChallengeReference, Box<dyn ChallengeApplicator<C>>),
  >,
  c: &mut C::F,
  c_challenge: &Option<(ChallengeReference, Box<dyn ChallengeApplicator<C>>)>,
  challenges: &[Vec<C::F>],
) {
  for (product, (challenge, applicator)) in challenge_weights {
    let (weights, id) = match product {
      ProductReference::Left { product: id, variable: _ } => (&mut *WL, id),
      ProductReference::Right { product: id, variable: _ } => (&mut *WR, id),
      ProductReference::Output { product: id, variable: _ } => (&mut *WO, id),
    };
    weights.push((*id, applicator(&challenges[challenge.0])));
  }

  if let Some(c_challenge) = c_challenge {
    *c = c_challenge.1(&challenges[c_challenge.0 .0]);
  }
}

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
  left: usize,
  right: usize,
  variable: usize,
}

pub struct Circuit<'a, T: Transcript, C: Ciphersuite> {
  generators: ProofGenerators<'a, T, C>,

  prover: bool,

  commitments: usize,
  pub(crate) variables: Vec<Variable<C>>,

  products: Vec<Product>,
  bound_products: Vec<Vec<ProductReference>>,
  finalized_commitments: HashMap<VectorCommitmentReference, Option<(C::F, C::G)>>,
  challengers: HashMap<ChallengeReference, Box<dyn Challenger<T, C>>>,

  constraints: Vec<Constraint<C>>,
  variable_constraints: HashMap<VariableReference, Option<Constraint<C>>>,
  post_constraints: Vec<(Constraint<C>, Option<C::F>)>,
}

impl<'a, T: Transcript, C: Ciphersuite> Circuit<'a, T, C> {
  pub fn new(generators: ProofGenerators<'a, T, C>, prover: bool) -> Self {
    Self {
      generators,

      prover,

      commitments: 0,
      variables: vec![],

      products: vec![],
      bound_products: vec![],
      finalized_commitments: HashMap::new(),
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

  pub fn variable(&self, product: ProductReference) -> VariableReference {
    match product {
      ProductReference::Left { variable, .. } => VariableReference(variable),
      ProductReference::Right { variable, .. } => VariableReference(variable),
      ProductReference::Output { variable, .. } => VariableReference(variable),
    }
  }

  pub fn variable_to_product(&self, variable: VariableReference) -> Option<ProductReference> {
    if let Variable::Product(product, _) = self.variables[variable.0] {
      return Some(ProductReference::Output { product, variable: variable.0 });
    }

    for (product_id, product) in self.products.iter().enumerate() {
      let Product { left: l, right: r, variable: this_variable } = product;

      if !((variable.0 == *l) || (variable.0 == *r)) {
        continue;
      }

      if let Variable::Product(var_product_id, _) = self.variables[*this_variable] {
        debug_assert_eq!(var_product_id, product_id);
        if variable.0 == *l {
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
      if (a.0 == product.left) && (b.0 == product.right) {
        return (
          (
            ProductReference::Left { product: id, variable: a.0 },
            ProductReference::Right { product: id, variable: b.0 },
            ProductReference::Output { product: id, variable: product.variable },
          ),
          VariableReference(product.variable),
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
      ProductReference::Left { product: product_id, variable: a.0 },
      ProductReference::Right { product: product_id, variable: b.0 },
      ProductReference::Output { product: product_id, variable: variable.0 },
    );

    self.products.push(Product { left: a.0, right: b.0, variable: variable.0 });
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
      if self.prover { Some(self.unchecked_value(self.variable(a))) } else { None },
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

  /// Allocate a vector commitment ID.
  pub fn allocate_vector_commitment(&mut self) -> VectorCommitmentReference {
    let res = VectorCommitmentReference(self.bound_products.len());
    self.bound_products.push(vec![]);
    res
  }

  /// Bind a product variable into a vector commitment, using the specified generator.
  ///
  /// If no generator is specified, the proof's existing generator will be used. This allows
  /// isolating the variable, prior to the circuit, without caring for how it was isolated.
  pub fn bind(
    &mut self,
    vector_commitment: VectorCommitmentReference,
    products: Vec<ProductReference>,
    generators: Option<&VectorCommitmentGenerators<T, C>>,
  ) {
    assert!(!self.finalized_commitments.contains_key(&vector_commitment));

    for product in &products {
      self.bound_products[vector_commitment.0].push(*product);
    }

    if let Some(generators) = generators {
      let mut to_replace = Vec::with_capacity(products.len());
      for product in products {
        // TODO: PR -> (GenList, usize) helper
        to_replace.push(match product {
          ProductReference::Left { product, .. } => (GeneratorsList::GBold1, product),
          ProductReference::Right { product, .. } => (GeneratorsList::HBold1, product),
          ProductReference::Output { product, .. } => (GeneratorsList::GBold2, product),
        });
      }

      self.generators.replace_generators(generators, to_replace);
    }
  }

  /// Finalize a vector commitment, returning it, preventing further binding.
  pub fn finalize_commitment(
    &mut self,
    vector_commitment: VectorCommitmentReference,
    blind: Option<C::F>,
  ) -> Option<C::G> {
    if self.prover() {
      if let Some(blind) = blind {
        // Calculate and return the vector commitment
        let products = self.bound_products[vector_commitment.0].clone();
        let mut terms = Vec::with_capacity(products.len() + 1);
        terms.push((blind, self.generators.h().point()));
        for product in products {
          match product {
            ProductReference::Left { product, variable } => {
              terms.push((
                self.variables[variable].value().unwrap(),
                self.generators.generator(GeneratorsList::GBold1, product).point(),
              ));
            }
            ProductReference::Right { product, variable } => {
              terms.push((
                self.variables[variable].value().unwrap(),
                self.generators.generator(GeneratorsList::HBold1, product).point(),
              ));
            }
            ProductReference::Output { product, variable } => {
              terms.push((
                self.variables[variable].value().unwrap(),
                self.generators.generator(GeneratorsList::GBold2, product).point(),
              ));
            }
          };
        }
        let commitment = multiexp(&terms);
        assert!(self
          .finalized_commitments
          .insert(vector_commitment, Some((blind, commitment)))
          .is_none());
        terms.zeroize();
        Some(commitment)
      } else {
        assert!(self.finalized_commitments.insert(vector_commitment, None).is_none());
        None
      }
    } else {
      assert!(blind.is_none());
      assert!(self.finalized_commitments.insert(vector_commitment, None).is_none());
      None
    }
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
    assert!(
      self.challengers.insert(challenge_ref, challenger).is_none(),
      "challenger already defined for this vector commitment"
    );
    if self.prover() {
      (
        challenge_ref,
        Some(challenger(commitment_challenge::<T, C>(
          self
            .finalized_commitments
            .get(&commitment)
            .expect("vector commitment wasn't finalized")
            .expect("prover didn't specify vector commitment's blind")
            .1,
        ))),
      )
    } else {
      (challenge_ref, None)
    }
  }

  // TODO: This can be optimized with post-processing passes
  fn compile(
    self,
  ) -> (
    ProofGenerators<'a, T, C>,
    Option<Vec<C::G>>,
    ScalarMatrix<C>,
    ScalarMatrix<C>,
    ScalarMatrix<C>,
    ScalarMatrix<C>,
    ScalarVector<C>,
    HashMap<ChallengeReference, Box<dyn Challenger<T, C>>>,
    Vec<HashMap<ProductReference, (ChallengeReference, Box<dyn ChallengeApplicator<C>>)>>,
    Vec<Option<(ChallengeReference, Box<dyn ChallengeApplicator<C>>)>>,
    Vec<Vec<(Option<C::F>, (GeneratorsList, usize))>>,
    Vec<(Option<C::F>, (GeneratorsList, usize))>,
    Option<ArithmeticCircuitWitness<C>>,
  ) {
    let (commitments, witness) = if self.prover {
      let mut aL = vec![];
      let mut aR = vec![];

      let mut commitments = vec![];
      let mut v = vec![];
      let mut gamma = vec![];

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
            aL.push(self.variables[product.left].value().unwrap());
            aR.push(self.variables[product.right].value().unwrap());
          }
        }
      }

      (
        Some(commitments),
        Some(ArithmeticCircuitWitness::new(
          ScalarVector(aL),
          ScalarVector(aR),
          ScalarVector(v),
          ScalarVector(gamma),
        )),
      )
    } else {
      (None, None)
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

    // WL, WR, WO, WV, c
    let mut WL = ScalarMatrix::new(n);
    let mut WR = ScalarMatrix::new(n);
    let mut WO = ScalarMatrix::new(n);
    let mut WV = ScalarMatrix::new(V_len);
    let mut c = Vec::with_capacity(n);
    let mut challenge_weights = Vec::with_capacity(n);
    let mut c_challenges = Vec::with_capacity(n);

    for constraint in self.constraints {
      // WL aL WR aR WO aO == WV v + c
      let mut eval = C::F::ZERO;

      let mut this_wl = vec![];
      let mut this_wr = vec![];
      let mut this_wo = vec![];
      let mut this_wv = vec![];

      for wl in constraint.WL {
        if self.prover {
          eval += wl.1 * witness.as_ref().unwrap().aL[wl.0];
        }
        this_wl.push(wl);
      }
      for wr in constraint.WR {
        if self.prover {
          eval += wr.1 * witness.as_ref().unwrap().aR[wr.0];
        }
        this_wr.push(wr);
      }
      for wo in constraint.WO {
        if self.prover {
          eval += wo.1 * (witness.as_ref().unwrap().aL[wo.0] * witness.as_ref().unwrap().aR[wo.0]);
        }
        this_wo.push(wo);
      }
      for wv in constraint.WV {
        if self.prover {
          eval -= wv.1 * witness.as_ref().unwrap().v[wv.0];
        }
        this_wv.push(wv);
      }

      if constraint.challenge_weights.is_empty() && constraint.c_challenge.is_none() && self.prover
      {
        assert_eq!(eval, constraint.c, "faulty constraint: {}", constraint.label);
      }

      WL.push(this_wl);
      WR.push(this_wr);
      WO.push(this_wo);
      WV.push(this_wv);
      c.push(constraint.c);
      challenge_weights.push(constraint.challenge_weights);
      c_challenges.push(constraint.c_challenge);
    }

    for (constraint, value) in self.post_constraints {
      WL.push(constraint.WL);
      WR.push(constraint.WR);
      WO.push(constraint.WO);
      assert!(constraint.WV.is_empty());
      WV.push(vec![]);
      if self.prover {
        c.push(value.unwrap());
      }
      challenge_weights.push(constraint.challenge_weights);
      c_challenges.push(constraint.c_challenge);
    }

    // The A commitment is g1 aL, g2 aO, h1 aR
    // Override the generators used for these products, if they were bound to a specific generator
    // Also tracks the variables relevant to vector commitments and the variables not
    let mut vc_used = HashSet::new();
    let mut vector_commitments = vec![vec![]; self.bound_products.len()];
    let mut others = vec![];
    for (vc, bindings) in self.bound_products.iter().enumerate() {
      for product in bindings {
        match *product {
          ProductReference::Left { product, .. } => {
            let gen = (GeneratorsList::GBold1, product);
            vc_used.insert(gen);
            vector_commitments[vc].push((witness.as_ref().map(|witness| witness.aL[product]), gen));
          }
          ProductReference::Right { product, .. } => {
            let gen = (GeneratorsList::HBold1, product);
            vc_used.insert(gen);
            vector_commitments[vc].push((witness.as_ref().map(|witness| witness.aR[product]), gen));
          }
          ProductReference::Output { product, .. } => {
            let gen = (GeneratorsList::GBold2, product);
            vc_used.insert(gen);
            vector_commitments[vc].push((
              witness.as_ref().map(|witness| witness.aL[product] * witness.aR[product]),
              gen,
            ));
          }
        }
      }
    }

    fn add_to_others<C: Ciphersuite, I: Iterator<Item = Option<C::F>>>(
      list: GeneratorsList,
      vars: I,
      vc_used: &HashSet<(GeneratorsList, usize)>,
      others: &mut Vec<(Option<C::F>, (GeneratorsList, usize))>,
    ) {
      for (p, var) in vars.enumerate() {
        if !vc_used.contains(&(list, p)) {
          others.push((var, (list, p)));
        }
      }
    }
    add_to_others::<C, _>(
      GeneratorsList::GBold1,
      (0 .. self.products.len()).map(|i| witness.as_ref().map(|witness| witness.aL[i])),
      &vc_used,
      &mut others,
    );
    add_to_others::<C, _>(
      GeneratorsList::HBold1,
      (0 .. self.products.len()).map(|i| witness.as_ref().map(|witness| witness.aR[i])),
      &vc_used,
      &mut others,
    );
    add_to_others::<C, _>(
      GeneratorsList::GBold2,
      (0 .. self.products.len())
        .map(|i| witness.as_ref().map(|witness| witness.aL[i] * witness.aR[i])),
      &vc_used,
      &mut others,
    );

    (
      self.generators,
      commitments,
      WL,
      WR,
      WO,
      WV,
      ScalarVector(c),
      self.challengers,
      challenge_weights,
      c_challenges,
      vector_commitments,
      others,
      witness,
    )
  }

  pub fn prove<R: RngCore + CryptoRng>(
    self,
    rng: &mut R,
    transcript: &mut T,
  ) -> (Vec<C::G>, ArithmeticCircuitProof<C>) {
    assert!(self.prover);
    let (generators, V, WL, WR, WO, WV, c, _, _, _, vector_commitments, _, witness) =
      self.compile();

    // TODO: Transcript all constraints

    assert!(vector_commitments.is_empty());
    (
      V.clone().unwrap(),
      ArithmeticCircuitStatement::new(generators, PointVector(V.unwrap()), WL, WR, WO, WV, c)
        .prove(rng, transcript, witness.unwrap()),
    )
  }

  fn vector_commitment_statement<GB: Clone + AsRef<[MultiexpPoint<C::G>]>>(
    alt_generators: InnerProductGenerators<'a, T, C, GB>,
    transcript: &mut T,
    commitment: C::G,
  ) -> WipStatement<'a, T, C, GB> {
    // TODO: Do we need to transcript more before this? Should we?
    let y = C::hash_to_F(b"vector_commitment_proof", transcript.challenge(b"y").as_ref());

    WipStatement::new(alt_generators, commitment, y)
  }

  pub fn verification_statement(self) -> ArithmeticCircuitWithoutVectorCommitments<'a, T, C> {
    assert!(!self.prover);
    let (proof_generators, _, WL, WR, WO, WV, c, _, _, _, vector_commitments, _, _) =
      self.compile();
    assert!(vector_commitments.is_empty());
    ArithmeticCircuitWithoutVectorCommitments { proof_generators, WL, WR, WO, WV, c }
  }

  // Returns the blinds used, the blinded vector commitments, the proof, and proofs the vector
  // commitments are well formed
  // TODO: Create a dedicated struct for this return value
  pub fn prove_with_vector_commitments<R: RngCore + CryptoRng>(
    self,
    rng: &mut R,
    transcript: &mut T,
  ) -> (Vec<C::G>, Vec<C::F>, Vec<C::G>, ArithmeticCircuitProof<C>, Vec<(WipProof<C>, WipProof<C>)>)
  {
    assert!(self.prover);

    let finalized_commitments = self.finalized_commitments.clone();
    let (
      proof_generators,
      V,
      mut WL,
      mut WR,
      mut WO,
      WV,
      mut c,
      challengers,
      challenge_weights,
      c_challenges,
      mut vector_commitments,
      others,
      witness,
    ) = self.compile();
    assert!(!vector_commitments.is_empty());
    let witness = witness.unwrap();

    /*
      In lieu of a proper vector commitment scheme, the following is done.

      The arithmetic circuit proof takes in a commitment of all product statements.
      That commitment is of the form left G1, right H1, out G2.

      Each vector commitment is for a series of variables against specfic generators.

      For each required vector commitment, a proof of a known DLog for the commitment, against the
      specified generators, is provided via a pair of WIP proofs.

      Finally, another pair of WIP proofs proves a known DLog for the remaining generators in this
      arithmetic circuit proof.

      The arithmetic circuit's in-proof commitment is then defined as the sum of the commitments
      and the commitment to the remaining variables.

      This forces the commitment to commit as the vector commitments do.

      The security of this is assumed. Technically, the commitment being well-formed isn't
      guaranteed by the Weighted Inner Product relationship. A formal proof of the security of this
      requires that property being proven. Such a proof may already exist as part of the WIP proof.

      TODO

      As one other note, a single WIP proof is likely fine, with parallelized g_bold/h_bold, if the
      prover provides the G component and a Schnorr PoK for it. While they may lie, leaving the G
      component, that shouldn't create any issues so long as G is distinct for all such proofs.

      That wasn't done here as it further complicates a complicated enough already scheme.
    */

    fn well_formed<
      'a,
      R: RngCore + CryptoRng,
      C: Ciphersuite,
      T: Transcript,
      GB: Clone + AsRef<[MultiexpPoint<C::G>]>,
    >(
      rng: &mut R,
      alt_generators_1: InnerProductGenerators<'a, T, C, GB>,
      alt_generators_2: InnerProductGenerators<'a, T, C, GB>,
      transcript: &mut T,
      scalars: Vec<C::F>,
      blind: C::F,
    ) -> (C::G, (WipProof<C>, WipProof<C>)) {
      assert_eq!(alt_generators_1.len(), scalars.len());

      let commitment = {
        let mut terms = Vec::with_capacity(1 + scalars.len());
        terms.push((blind, alt_generators_1.h().point()));
        for (i, scalar) in scalars.iter().enumerate() {
          terms.push((*scalar, alt_generators_1.generator(GeneratorsList::GBold1, i).point()));
        }
        let res = multiexp(&terms);
        terms.zeroize();
        res
      };

      let b = ScalarVector(vec![C::F::ZERO; scalars.len()]);
      let witness = WipWitness::<C>::new(ScalarVector(scalars), b, blind);

      transcript.append_message(b"vector_commitment", commitment.to_bytes());
      (
        commitment,
        (
          {
            Circuit::<T, C>::vector_commitment_statement(alt_generators_1, transcript, commitment)
              .prove(&mut *rng, transcript, witness.clone())
          },
          {
            Circuit::<T, C>::vector_commitment_statement(alt_generators_2, transcript, commitment)
              .prove(&mut *rng, transcript, witness)
          },
        ),
      )
    }

    let mut blinds = vec![];
    let mut commitments = vec![];
    let mut proofs = vec![];
    for (vc, vector_commitment) in vector_commitments.drain(..).enumerate() {
      let mut scalars = vec![];
      let mut generators = vec![];
      for (var, gen) in vector_commitment {
        scalars.push(var.unwrap());
        generators.push(gen);
      }
      blinds.push(
        finalized_commitments
          .get(&VectorCommitmentReference(vc))
          .and_then(|present| present.map(|(blind, _)| blind))
          .unwrap_or(C::F::random(&mut *rng)),
      );

      let vc_generators = proof_generators.vector_commitment_generators(generators);
      let (commitment, proof) = well_formed::<_, C, _, _>(
        &mut *rng,
        vc_generators.0,
        vc_generators.1,
        transcript,
        scalars,
        blinds[blinds.len() - 1],
      );
      commitments.push(commitment);
      proofs.push(proof);
    }
    let vector_commitments = commitments;

    let mut challenges = vec![vec![]; vector_commitments.len()];
    for (challenge, challenger) in challengers {
      challenges[challenge.0] =
        challenger(commitment_challenge::<T, C>(vector_commitments[challenge.0]));
    }
    for (i, (challenge_weights, c_challenge)) in
      challenge_weights.iter().zip(c_challenges.iter()).enumerate()
    {
      embed_challenges(
        &mut WL.data[i],
        &mut WR.data[i],
        &mut WO.data[i],
        challenge_weights,
        &mut c[i],
        c_challenge,
        &challenges,
      );
    }

    // Push one final WIP proof for all other variables
    let other_commitment;
    let other_blind = C::F::random(&mut *rng);
    {
      let mut scalars = vec![];
      let mut generators = vec![];
      for (scalar, generator) in others {
        scalars.push(scalar.unwrap());
        generators.push(generator);
      }
      let vc_generators = proof_generators.vector_commitment_generators(generators);
      let proof;
      (other_commitment, proof) = well_formed::<_, C, _, _>(
        &mut *rng,
        vc_generators.0,
        vc_generators.1,
        transcript,
        scalars,
        other_blind,
      );
      proofs.push(proof);
    }

    let proof = ArithmeticCircuitStatement::new(
      proof_generators,
      PointVector(V.clone().unwrap()),
      WL,
      WR,
      WO,
      WV,
      c,
    )
    .prove_with_blind(rng, transcript, witness, blinds.iter().sum::<C::F>() + other_blind);
    debug_assert_eq!(proof.A, vector_commitments.iter().sum::<C::G>() + other_commitment);

    (V.unwrap(), blinds, vector_commitments, proof, proofs)
  }

  pub fn verification_statement_with_vector_commitments(
    self,
  ) -> ArithmeticCircuitWithVectorCommitments<'a, T, C, impl Clone + AsRef<[MultiexpPoint<C::G>]>>
  {
    assert!(!self.prover);
    let (
      proof_generators,
      _,
      WL,
      WR,
      WO,
      WV,
      c,
      challengers,
      challenge_weights,
      c_challenges,
      mut vector_commitments_data,
      mut others,
      _,
    ) = self.compile();

    let mut vector_commitment_generators = vec![];
    for mut data in vector_commitments_data.drain(..) {
      vector_commitment_generators.push(
        proof_generators.vector_commitment_generators(data.drain(..).map(|(_, gen)| gen).collect()),
      );
    }
    vector_commitment_generators.push(
      proof_generators.vector_commitment_generators(others.drain(..).map(|(_, gen)| gen).collect()),
    );

    ArithmeticCircuitWithVectorCommitments {
      proof_generators,
      vector_commitment_generators,

      challengers,
      WL,
      WR,
      WO,
      WV,
      c,
      challenge_weights,
      c_challenges,
    }
  }
}

pub struct ArithmeticCircuitWithoutVectorCommitments<'a, T: Transcript, C: Ciphersuite> {
  proof_generators: ProofGenerators<'a, T, C>,

  WL: ScalarMatrix<C>,
  WR: ScalarMatrix<C>,
  WO: ScalarMatrix<C>,
  WV: ScalarMatrix<C>,
  c: ScalarVector<C>,
}

impl<'a, T: Transcript, C: Ciphersuite> ArithmeticCircuitWithoutVectorCommitments<'a, T, C> {
  pub fn verify<R: RngCore + CryptoRng>(
    &self,
    rng: &mut R,
    verifier: &mut BatchVerifier<(), C::G>,
    transcript: &mut T,
    commitments: Vec<C::G>,
    post_values: &[C::F],
    proof: ArithmeticCircuitProof<C>,
  ) {
    let mut c = self.c.clone();
    assert_eq!(c.len() + post_values.len(), self.WL.length());
    for post in post_values {
      c.0.push(*post);
    }

    ArithmeticCircuitStatement::new(
      self.proof_generators.clone(),
      PointVector(commitments),
      self.WL.clone(),
      self.WR.clone(),
      self.WO.clone(),
      self.WV.clone(),
      c,
    )
    .verify(rng, verifier, transcript, proof)
  }
}

pub struct ArithmeticCircuitWithVectorCommitments<
  'a,
  T: Transcript,
  C: Ciphersuite,
  GB: Clone + AsRef<[MultiexpPoint<C::G>]>,
> {
  proof_generators: ProofGenerators<'a, T, C>,
  vector_commitment_generators:
    Vec<(InnerProductGenerators<'a, T, C, GB>, InnerProductGenerators<'a, T, C, GB>)>,

  challengers: HashMap<ChallengeReference, Box<dyn Challenger<T, C>>>,
  WL: ScalarMatrix<C>,
  WR: ScalarMatrix<C>,
  WO: ScalarMatrix<C>,
  WV: ScalarMatrix<C>,
  c: ScalarVector<C>,
  challenge_weights:
    Vec<HashMap<ProductReference, (ChallengeReference, Box<dyn ChallengeApplicator<C>>)>>,
  c_challenges: Vec<Option<(ChallengeReference, Box<dyn ChallengeApplicator<C>>)>>,
}

impl<'a, T: Transcript, C: Ciphersuite, GB: Clone + AsRef<[MultiexpPoint<C::G>]>>
  ArithmeticCircuitWithVectorCommitments<'a, T, C, GB>
{
  pub fn verify<R: RngCore + CryptoRng>(
    &self,
    rng: &mut R,
    verifier: &mut BatchVerifier<(), C::G>,
    transcript: &mut T,
    commitments: Vec<C::G>,
    mut vector_commitments: Vec<C::G>,
    post_values: &[C::F],
    proof: ArithmeticCircuitProof<C>,
    mut vc_proofs: Vec<(WipProof<C>, WipProof<C>)>,
  ) {
    let vc_sum = vector_commitments.iter().sum::<C::G>();
    let mut verify_wip =
      |wip_generators: &(InnerProductGenerators<_, _, _>, InnerProductGenerators<_, _, _>),
       commitment: C::G,
       proofs: (_, _)| {
        transcript.append_message(b"vector_commitment", commitment.to_bytes());
        Circuit::vector_commitment_statement(wip_generators.0.clone(), transcript, commitment)
          .verify(rng, verifier, transcript, proofs.0);
        Circuit::vector_commitment_statement(wip_generators.1.clone(), transcript, commitment)
          .verify(rng, verifier, transcript, proofs.1);
      };

    // TODO: Make sure this has the expected amount of commitments

    // Make sure this had the expected amount of vector commitments.
    assert_eq!(vector_commitments.len(), self.vector_commitment_generators.len() - 1);
    assert_eq!(vc_proofs.len(), self.vector_commitment_generators.len());

    // Apply the post-values
    let mut c = self.c.clone();
    assert_eq!(self.c.len() + post_values.len(), self.WL.length());
    for post in post_values {
      c.0.push(*post);
    }

    let mut challenges = vec![vec![]; vector_commitments.len()];
    for (challenge, challenger) in &self.challengers {
      challenges[challenge.0] =
        challenger(commitment_challenge::<T, C>(vector_commitments[challenge.0]));
    }

    for ((generators, commitment), proofs) in self.vector_commitment_generators
      [.. self.vector_commitment_generators.len() - 1]
      .iter()
      .zip(vector_commitments.drain(..))
      .zip(vc_proofs.drain(.. (vc_proofs.len() - 1)))
    {
      verify_wip(generators, commitment, proofs);
    }
    assert_eq!(vc_proofs.len(), 1);
    verify_wip(
      self.vector_commitment_generators.last().as_ref().unwrap(),
      proof.A - vc_sum,
      vc_proofs.swap_remove(0),
    );

    let mut WL = self.WL.clone();
    let mut WR = self.WR.clone();
    let mut WO = self.WO.clone();
    let WV = self.WV.clone();

    for (i, (challenge_weights, c_challenge)) in
      self.challenge_weights.iter().zip(self.c_challenges.iter()).enumerate()
    {
      embed_challenges(
        &mut WL.data[i],
        &mut WR.data[i],
        &mut WO.data[i],
        challenge_weights,
        &mut c[i],
        c_challenge,
        &challenges,
      );
    }

    ArithmeticCircuitStatement::new(
      self.proof_generators.clone(),
      PointVector(commitments),
      WL,
      WR,
      WO,
      WV,
      c,
    )
    .verify(rng, verifier, transcript, proof)
  }
}
