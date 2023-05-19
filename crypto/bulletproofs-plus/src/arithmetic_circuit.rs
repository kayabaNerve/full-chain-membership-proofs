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

#[derive(Clone, Debug, Zeroize, ZeroizeOnDrop)]
pub enum Variable<C: BulletproofsCurve> {
  Constant(C::F),
  Secret(Option<C::F>),
  Committed(Option<Commitment<C>>, C::G),
  Product(usize, Option<C::F>),
}

#[derive(Copy, Clone, PartialEq, Eq, Debug, Zeroize)]
pub struct VariableReference(usize);
#[derive(Copy, Clone, PartialEq, Eq, Debug, Zeroize)]
pub enum ProductReference {
  Left { product: usize, variable: usize },
  Right { product: usize, variable: usize },
  Output { product: usize, variable: usize },
}
#[derive(Copy, Clone, Debug, Zeroize)]
pub struct CommitmentReference(usize);

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
      ProductReference::Left { product: id, variable: _ } => (&mut self.WL, id),
      ProductReference::Right { product: id, variable: _ } => (&mut self.WR, id),
      ProductReference::Output { product: id, variable: _ } => (&mut self.WO, id),
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
  pub fn rhs_offset(&mut self, offset: C::F) -> &mut Self {
    assert!(bool::from(self.c.is_zero()));
    self.c = offset;
    self
  }
}

impl<C: BulletproofsCurve> Variable<C> {
  pub fn value(&self) -> Option<C::F> {
    match self {
      Variable::Constant(value) => Some(*value),
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

pub struct Circuit<C: BulletproofsCurve> {
  g_bold1: PointVector<C>,
  g_bold2: PointVector<C>,
  h_bold1: PointVector<C>,
  h_bold2: PointVector<C>,

  prover: bool,

  commitments: usize,
  variables: Vec<Variable<C>>,

  products: Vec<Product>,

  constraints: Vec<Constraint<C>>,
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

      commitments: 0,
      variables: vec![],

      products: vec![],

      constraints: vec![],
    }
  }

  pub fn prover(&self) -> bool {
    self.prover
  }

  /// Obtain the underlying variable from a reference.
  ///
  /// This requires a constraint to be safely used.
  pub fn unchecked_variable(&self, variable: VariableReference) -> Variable<C> {
    self.variables[variable.0].clone()
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
        assert_eq!(var_product_id, product_id);
        if variable.0 == *l {
          return Some(ProductReference::Left { product: product_id, variable: *this_variable });
        } else {
          return Some(ProductReference::Right { product: product_id, variable: *this_variable });
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
          VariableReference(product.variable)
        );
      }
    }

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
    let mut found_l = false;
    let mut found_r = false;

    let var_ref = |prod| match prod {
      ProductReference::Left { variable, .. } => variable,
      ProductReference::Right { variable, .. } => variable,
      ProductReference::Output { variable, .. } => variable,
    };

    {
      let mut try_constraint = |circuit: &mut Circuit<C>,
                                (e_p, existing_product): (usize, Product),
                                new: ProductReference| {
        let Product { left: l, right: r, variable } = existing_product;
        let new_var = var_ref(new);
        if (!found_l) && (l == new_var) {
          let prod = ProductReference::Left { product: e_p, variable };
          circuit.constrain_equality(prod, new);
          // Only add a single consistency constraint, as all other uses are assumed to be already
          // consistent
          found_l = true;
        }
        if (!found_r) && (r == new_var) {
          let prod = ProductReference::Right { product: e_p, variable };
          circuit.constrain_equality(prod, new);
          found_r = true;
        }
      };

      // Only iterate over the products before this freshly added product
      let products_clone =
        self.products.iter().take(product_id).cloned().enumerate().collect::<Vec<_>>();
      for product in products_clone {
        try_constraint(self, product.clone(), products.0);
        try_constraint(self, product, products.1);
      }
    }

    // If this variable is itself an output, form the constraint that way
    let mut output_consistency = |var: ProductReference| {
      if let Variable::Product(product, _) = self.variables[var_ref(var)] {
        self.constrain_equality(ProductReference::Output { product, variable: var_ref(var) }, var);
      }
    };
    if !found_l {
      output_consistency(products.0);
    }
    if !found_r {
      output_consistency(products.1);
    }

    (products, variable)
  }

  // TODO: Optimize this out. We shouldn't need a variable for something native to the constraint
  pub fn add_constant(&mut self, constant: C::F) -> VariableReference {
    // Return the existing constant, if there's already one
    for (i, variable) in self.variables.iter().enumerate() {
      if let Variable::Constant(value) = variable {
        if *value == constant {
          return VariableReference(i);
        }
      }
    }

    let res = VariableReference(self.variables.len());
    self.variables.push(Variable::Constant(constant));

    // Immediately add a product statement for this so we can perform the initial constraint
    let ((product, _, _), _) = self.product(res, res);
    let mut constraint = Constraint::new("constant");
    constraint.weight(product, C::F::ONE);
    constraint.rhs_offset(constant);
    self.constraints.push(constraint);

    res
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
      assert_eq!(commitment.calculate(), actual);
    }

    let res = CommitmentReference(self.commitments);
    self.commitments += 1;
    self.variables.push(Variable::Committed(commitment, actual));
    res
  }

  /// Create, and constrain, a variable to be the sum of two other variables.
  pub fn add(&mut self, a: VariableReference, b: VariableReference) -> VariableReference {
    let left = &self.variables[a.0];
    let right = &self.variables[b.0];

    if let (Variable::Constant(left), Variable::Constant(right)) = (left, right) {
      return self.add_constant(*left + right);
    }

    let res = VariableReference(self.variables.len());
    self.variables.push(Variable::Secret(
      Some(()).filter(|_| self.prover).map(|_| left.value().unwrap() + right.value().unwrap()),
    ));

    let mut product_refs = vec![self.variable_to_product(a), self.variable_to_product(b)];
    // Since neither of these have been prior referenced, we have 3 variables needing constraining
    // That requires two mul statements
    if product_refs == [None, None] {
      let ((l, r, _), _) = self.product(a, b);
      product_refs = vec![Some(l), Some(r)];
    }

    let other = if product_refs[0].is_none() { a } else { b };

    // Create the second mul statement
    let ((sum_ref, r, _), _) = self.product(res, other);
    if product_refs[0].is_none() {
      product_refs[0] = Some(r);
    } else if product_refs[1].is_none() {
      product_refs[1] = Some(r);
    }

    // Constrain the sum
    let mut constraint = Constraint::new("sum");
    constraint.weight(sum_ref, -C::F::ONE);
    constraint.weight(product_refs[0].unwrap(), C::F::ONE);
    constraint.weight(product_refs[1].unwrap(), C::F::ONE);
    self.constrain(constraint);

    res
  }

  /// Add a constraint.
  pub fn constrain(&mut self, constraint: Constraint<C>) {
    self.constraints.push(constraint);
  }

  pub fn constrain_equality(&mut self, a: ProductReference, b: ProductReference) {
    if a == b {
      return;
    }

    let mut constraint = Constraint::new("equality");
    constraint.weight(a, C::F::ONE);
    constraint.weight(b, -C::F::ONE);
    self.constrain(constraint);
  }

  // TODO: This can be significantly optimized with post-processing passes
  fn compile(self) -> (ArithmeticCircuitStatement<C>, Option<ArithmeticCircuitWitness<C>>) {
    let witness = if self.prover {
      let mut aL = vec![];
      let mut aR = vec![];

      let mut v = vec![];
      let mut gamma = vec![];

      for variable in self.variables.iter() {
        match variable {
          Variable::Constant(_) => {}
          Variable::Secret(_) => {}
          Variable::Committed(value, actual) => {
            let value = value.as_ref().unwrap();
            assert_eq!(value.calculate(), *actual);
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
        Variable::Constant(_) => {}
        Variable::Secret(_) => {}
        Variable::Committed(_, actual) => V.push(*actual),
        Variable::Product(_, _) => n += 1,
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
