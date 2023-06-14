use std::collections::{HashSet, HashMap, BTreeSet};

use zeroize::{Zeroize, ZeroizeOnDrop};
use rand_core::{RngCore, CryptoRng};

use transcript::Transcript;

use multiexp::BatchVerifier;
use ciphersuite::{
  group::{ff::Field, GroupEncoding},
  Ciphersuite,
};

use crate::{
  ScalarVector, ScalarMatrix, PointVector, VectorCommitmentGenerators, GeneratorsList, Generators,
  weighted_inner_product::*, arithmetic_circuit_proof,
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
  Committed(Option<Commitment<C>>, C::G),
  Product(usize, Option<C::F>),
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug, Zeroize)]
pub struct VariableReference(usize);
// TODO: Remove Ord and usage of HashMaps/BTreeSets
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Zeroize)]
pub enum ProductReference {
  Left { product: usize, variable: usize },
  Right { product: usize, variable: usize },
  Output { product: usize, variable: usize },
}
#[derive(Copy, Clone, Debug, Zeroize)]
pub struct CommitmentReference(usize);
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug, Zeroize)]
pub struct VectorCommitmentReference(usize);

#[derive(Clone, Debug)]
pub struct Constraint<C: Ciphersuite> {
  label: &'static str,
  // Each weight (C::F) is bound to a specific variable (usize) to allow post-expansion to valid
  // constraints
  WL: Vec<(usize, C::F)>,
  WR: Vec<(usize, C::F)>,
  WO: Vec<(usize, C::F)>,
  WV: Vec<(usize, C::F)>,
  c: C::F,
}

impl<C: Ciphersuite> Constraint<C> {
  pub fn new(label: &'static str) -> Self {
    Self { label, WL: vec![], WR: vec![], WO: vec![], WV: vec![], c: C::F::ZERO }
  }

  pub fn weight(&mut self, product: ProductReference, weight: C::F) -> &mut Self {
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
  pub fn weight_commitment(&mut self, variable: CommitmentReference, weight: C::F) -> &mut Self {
    for existing in &self.WV {
      assert!(existing.0 != variable.0);
    }
    self.WV.push((variable.0, weight));
    self
  }
  pub fn rhs_offset(&mut self, offset: C::F) -> &mut Self {
    self.c += offset;
    self
  }
}

impl<C: Ciphersuite> Variable<C> {
  pub fn value(&self) -> Option<C::F> {
    match self {
      Variable::Secret(value) => *value,
      // This branch should never be reachable due to usage of CommitmentReference
      Variable::Committed(_commitment, _) => {
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

pub struct Circuit<T: Transcript, C: Ciphersuite> {
  generators: Generators<T, C>,

  prover: bool,

  commitments: usize,
  pub(crate) variables: Vec<Variable<C>>,

  products: Vec<Product>,
  bound_products: Vec<BTreeSet<ProductReference>>,
  finalized_commitments: HashMap<VectorCommitmentReference, Option<C::F>>,
  vector_commitments: Option<Vec<C::G>>,

  constraints: Vec<Constraint<C>>,
  variable_constraints: HashMap<VariableReference, Option<Constraint<C>>>,
}

impl<T: Transcript, C: Ciphersuite> Circuit<T, C> {
  pub fn new(
    generators: Generators<T, C>,
    prover: bool,
    vector_commitments: Option<Vec<C::G>>,
  ) -> Self {
    assert_eq!(prover, vector_commitments.is_none());

    Self {
      generators,

      prover,

      commitments: 0,
      variables: vec![],

      products: vec![],
      bound_products: vec![],
      finalized_commitments: HashMap::new(),
      vector_commitments,

      constraints: vec![],
      variable_constraints: HashMap::new(),
    }
  }

  pub fn prover(&self) -> bool {
    self.prover
  }

  pub fn h(&self) -> C::G {
    self.generators.h()
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
  pub fn add_committed_input(
    &mut self,
    commitment: Option<Commitment<C>>,
    actual: C::G,
  ) -> CommitmentReference {
    assert_eq!(self.prover, commitment.is_some());
    if let Some(commitment) = commitment.clone() {
      assert_eq!(commitment.calculate(self.generators.g(), self.generators.h()), actual);
    }

    let res = CommitmentReference(self.commitments);
    self.commitments += 1;
    self.variables.push(Variable::Committed(commitment, actual));
    res
  }

  /// Add a constraint.
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
    self.bound_products.push(BTreeSet::new());
    res
  }

  /// Bind a product variable into a vector commitment, using the specified generator.
  ///
  /// If no generator is specified, the proof's existing generator will be used. This allows
  /// isolating the variable, prior to the circuit, without caring for how it was isolated.
  // TODO: Batch bind, taking in a new VectorCommitmentsStruct for the generators
  pub fn bind(
    &mut self,
    vector_commitment: VectorCommitmentReference,
    products: Vec<ProductReference>,
    generators: Option<&VectorCommitmentGenerators<T, C>>,
  ) {
    assert!(!self.finalized_commitments.contains_key(&vector_commitment));

    for product in &products {
      for bound in &self.bound_products {
        assert!(!bound.contains(product));
      }
      self.bound_products[vector_commitment.0].insert(*product);
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

      self.generators.replace_generators(generators, &to_replace);
    }
  }

  /// Finalize a vector commitment, returning it, preventing further binding.
  pub fn finalize_commitment(
    &mut self,
    vector_commitment: VectorCommitmentReference,
    blind: Option<C::F>,
  ) -> C::G {
    if self.prover() {
      // Calculate and return the vector commitment
      // TODO: Use a multiexp here
      let mut commitment = self.generators.h() * blind.unwrap();
      for product in self.bound_products[vector_commitment.0].clone() {
        commitment += match product {
          ProductReference::Left { product, variable } => {
            self.generators.g_bold()[product] * self.variables[variable].value().unwrap()
          }
          ProductReference::Right { product, variable } => {
            self.generators.h_bold()[product] * self.variables[variable].value().unwrap()
          }
          ProductReference::Output { product, variable } => {
            self.generators.g_bold2()[product] * self.variables[variable].value().unwrap()
          }
        };
      }
      self.finalized_commitments.insert(vector_commitment, blind);
      commitment
    } else {
      assert!(blind.is_none());
      self.finalized_commitments.insert(vector_commitment, None);
      self.vector_commitments.as_ref().unwrap()[vector_commitment.0]
    }
  }

  // TODO: This can be optimized with post-processing passes
  // TODO: Don't run this on every single prove/verify. It should only be run once at compile time
  fn compile(
    self,
  ) -> (
    ArithmeticCircuitStatement<T, C>,
    Vec<Vec<(Option<C::F>, (GeneratorsList, usize))>>,
    Vec<(Option<C::F>, (GeneratorsList, usize))>,
    Option<ArithmeticCircuitWitness<C>>,
  ) {
    let witness = if self.prover {
      let mut aL = vec![];
      let mut aR = vec![];

      let mut v = vec![];
      let mut gamma = vec![];

      for variable in &self.variables {
        match variable {
          Variable::Secret(_) => {}
          Variable::Committed(value, actual) => {
            let value = value.as_ref().unwrap();
            assert_eq!(value.calculate(self.generators.g(), self.generators.h()), *actual);
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
        Variable::Secret(_) => {}
        Variable::Committed(_, actual) => V.push(*actual),
        Variable::Product(_, _) => n += 1,
      }
    }

    // WL, WR, WO, WV, c
    let mut WL = ScalarMatrix::new(n);
    let mut WR = ScalarMatrix::new(n);
    let mut WO = ScalarMatrix::new(n);
    let mut WV = ScalarMatrix::new(V.len());
    let mut c = vec![];

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

      if self.prover {
        assert_eq!(eval, constraint.c, "faulty constraint: {}", constraint.label);
      }

      WL.push(this_wl);
      WR.push(this_wr);
      WO.push(this_wo);
      WV.push(this_wv);
      c.push(constraint.c);
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
      ArithmeticCircuitStatement::new(
        self.generators,
        PointVector(V),
        WL,
        WR,
        WO,
        WV,
        ScalarVector(c),
      ),
      vector_commitments,
      others,
      witness,
    )
  }

  pub fn prove<R: RngCore + CryptoRng>(
    self,
    rng: &mut R,
    transcript: &mut T,
  ) -> ArithmeticCircuitProof<C> {
    assert!(self.prover);
    let (statement, vector_commitments, _, witness) = self.compile();
    assert!(vector_commitments.is_empty());
    statement.prove(rng, transcript, witness.unwrap())
  }

  fn vector_commitment_statement(
    alt_generators: Generators<T, C>,
    transcript: &mut T,
    commitment: C::G,
  ) -> WipStatement<T, C> {
    transcript.append_message(b"vector_commitment", commitment.to_bytes());

    // TODO: Do we need to transcript more before this? Should we?
    let y = C::hash_to_F(b"vector_commitment_proof", transcript.challenge(b"y").as_ref());

    WipStatement::new(alt_generators, commitment, y)
  }

  pub fn verify<R: RngCore + CryptoRng>(
    self,
    rng: &mut R,
    verifier: &mut BatchVerifier<(), C::G>,
    transcript: &mut T,
    proof: ArithmeticCircuitProof<C>,
  ) {
    assert!(!self.prover);
    assert!(self.vector_commitments.as_ref().unwrap().is_empty());
    let (statement, vector_commitments, _, _) = self.compile();
    assert!(vector_commitments.is_empty());
    statement.verify(rng, verifier, transcript, proof)
  }

  // Returns the blinds used, the blinded vector commitments, the proof, and proofs the vector
  // commitments are well formed
  // TODO: Create a dedicated struct for this return value
  pub fn prove_with_vector_commitments<R: RngCore + CryptoRng>(
    self,
    rng: &mut R,
    transcript: &mut T,
  ) -> (Vec<C::F>, Vec<C::G>, ArithmeticCircuitProof<C>, Vec<(WipProof<C>, WipProof<C>)>) {
    assert!(self.prover);

    let finalized_commitments = self.finalized_commitments.clone();
    let proof_generators = self.generators.clone();
    let (statement, mut vector_commitments, others, witness) = self.compile();
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

    fn well_formed<R: RngCore + CryptoRng, C: Ciphersuite, T: Transcript>(
      rng: &mut R,
      alt_generators_1: Generators<T, C>,
      alt_generators_2: Generators<T, C>,
      transcript: &mut T,
      scalars: Vec<C::F>,
      blind: C::F,
    ) -> (C::G, (WipProof<C>, WipProof<C>)) {
      assert_eq!(alt_generators_1.multiexp_g_bold().len(), scalars.len());
      assert!(alt_generators_1.multiexp_g_bold2().is_empty());
      assert!(alt_generators_1.multiexp_h_bold2().is_empty());

      let scalars_len = scalars.len();

      // TODO: Use a multiexp here
      let mut commitment = alt_generators_1.h() * blind;
      for (scalar, generator) in scalars.iter().zip(alt_generators_1.g_bold().0.iter()) {
        commitment += *generator * scalar;
      }

      let b = ScalarVector(vec![C::F::ZERO; scalars.len()]);
      let witness = WipWitness::<C>::new(ScalarVector(scalars), b, blind);

      (
        commitment,
        (
          {
            let statement = Circuit::<T, C>::vector_commitment_statement(
              alt_generators_1.reduce(scalars_len, false),
              transcript,
              commitment,
            );
            statement.prove(&mut *rng, transcript, witness.clone())
          },
          {
            let statement = Circuit::<T, C>::vector_commitment_statement(
              alt_generators_2.reduce(scalars_len, false),
              transcript,
              commitment,
            );
            statement.prove(&mut *rng, transcript, witness)
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
          .cloned()
          .unwrap_or(Some(C::F::random(&mut *rng)))
          .unwrap(),
      );

      let vc_generators = proof_generators.vector_commitment_generators(generators);
      let (commitment, proof) = well_formed::<_, C, _>(
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
      (other_commitment, proof) = well_formed::<_, C, _>(
        &mut *rng,
        vc_generators.0,
        vc_generators.1,
        transcript,
        scalars,
        other_blind,
      );
      proofs.push(proof);
    }

    let proof = statement.prove_with_blind(
      rng,
      transcript,
      witness,
      blinds.iter().sum::<C::F>() + other_blind,
    );
    debug_assert_eq!(proof.A, vector_commitments.iter().sum::<C::G>() + other_commitment);

    (blinds, vector_commitments, proof, proofs)
  }

  pub fn verify_with_vector_commitments<R: RngCore + CryptoRng>(
    self,
    rng: &mut R,
    verifier: &mut BatchVerifier<(), C::G>,
    transcript: &mut T,
    proof: ArithmeticCircuitProof<C>,
    mut vc_proofs: Vec<(WipProof<C>, WipProof<C>)>,
  ) {
    assert!(!self.prover);
    let vector_commitments = self.vector_commitments.clone().unwrap();
    let proof_generators = self.generators.clone();
    let (statement, mut vector_commitments_data, mut others, _) = self.compile();
    assert_eq!(vector_commitments.len(), vector_commitments_data.len());

    let mut verify_proofs = |generators: Vec<_>, commitment, proofs: (_, _)| {
      let gens_len = generators.len();
      let vc_generators = proof_generators.vector_commitment_generators(generators);
      let wip_statement = Self::vector_commitment_statement(
        vc_generators.0.reduce(gens_len, false),
        transcript,
        commitment,
      );
      wip_statement.verify(rng, verifier, transcript, proofs.0);

      let wip_statement = Self::vector_commitment_statement(
        vc_generators.1.reduce(gens_len, false),
        transcript,
        commitment,
      );
      wip_statement.verify(rng, verifier, transcript, proofs.1);
    };

    assert_eq!(vector_commitments.len() + 1, vc_proofs.len());
    for ((commitment, mut data), proofs) in vector_commitments
      .iter()
      .zip(vector_commitments_data.drain(..))
      .zip(vc_proofs.drain(.. (vc_proofs.len() - 1)))
    {
      verify_proofs(data.drain(..).map(|(_, gen)| gen).collect(), *commitment, proofs);
    }

    {
      assert_eq!(vc_proofs.len(), 1);
      verify_proofs(
        others.drain(..).map(|(_, gen)| gen).collect(),
        proof.A - vector_commitments.iter().sum::<C::G>(),
        vc_proofs.swap_remove(0),
      );
    }

    statement.verify(rng, verifier, transcript, proof);
  }
}
