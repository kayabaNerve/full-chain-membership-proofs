use rand_core::{RngCore, CryptoRng};

use zeroize::{Zeroize, ZeroizeOnDrop};

use transcript::Transcript;

use ciphersuite::{group::ff::Field, Ciphersuite};

use crate::{ScalarVector, ScalarMatrix, PointVector, arithmetic_circuit_proof::*};

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
    assert!(bool::from(self.c.is_zero()));
    self.c = offset;
    self
  }
}

impl<C: Ciphersuite> Variable<C> {
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

pub struct Circuit<C: Ciphersuite> {
  g: C::G,
  h: C::G,
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

impl<C: Ciphersuite> Circuit<C> {
  pub fn new(
    g: C::G,
    h: C::G,
    g_bold1: PointVector<C>,
    g_bold2: PointVector<C>,
    h_bold1: PointVector<C>,
    h_bold2: PointVector<C>,
    prover: bool,
  ) -> Self {
    Self {
      g,
      h,
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
    if let Some(existing) = existing_a_use {
      self.constrain_equality(products.0, existing);
    }
    if let Some(existing) = existing_b_use {
      self.constrain_equality(products.1, existing);
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
      assert_eq!(commitment.calculate(self.g, self.h), actual);
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

  pub fn constrain_equality(&mut self, a: ProductReference, b: ProductReference) {
    if a == b {
      return;
    }

    let mut constraint = Constraint::new("equality");
    constraint.weight(a, C::F::ONE);
    constraint.weight(b, -C::F::ONE);
    self.constrain(constraint);
  }

  fn remove_unused_products(&mut self) {
    let mut key = self.products.len() - 1;
    'unused_product: while key != 0 {
      if key == self.products.len() {
        key -= 1;
      }

      // Check if this product never had its output used
      for constraint in &self.constraints {
        for (i, _) in &constraint.WO {
          if *i == key {
            key -= 1;
            continue 'unused_product;
          }
        }
      }

      // Since this product's output was never used, its only utility is to allow the included
      // variables to be used in constraints

      // Check if other products can be used for that purpose
      {
        let has_other_product = |variable| {
          for (i, product) in self.products.iter().enumerate() {
            if key == i {
              continue;
            }

            if (product.left == variable) ||
              (product.right == variable) ||
              (product.variable == variable)
            {
              return true;
            }
          }
          false
        };
        if !(has_other_product(self.products[key].left) &&
          has_other_product(self.products[key].right))
        {
          key -= 1;
          continue;
        }
      }

      // Since this product is unused, and these variables can have their constraints moved to
      // other products, remove this product
      let removed = self.products.remove(key);

      let to_decrement_threshold = {
        // Find the variable for this product
        let mut i = 0;
        while match self.variables[i] {
          Variable::Product(product, _) => product != key,
          _ => true,
        } {
          i += 1;
        }

        // Remove it, marking the threshold
        match self.variables.remove(i) {
          Variable::Product(product, _) => debug_assert_eq!(key, product),
          _ => panic!("removed non-product variable"),
        }
        let to_decrement_threshold = i;

        // Shift down variables
        while i < self.variables.len() {
          match self.variables[i] {
            Variable::Constant(..) => {}
            Variable::Secret(..) => {}
            Variable::Committed(..) => {}
            Variable::Product(ref mut product, _) => {
              debug_assert!(*product > key);
              *product -= 1;
            }
          }

          i += 1;
        }
        to_decrement_threshold
      };

      // Get the variables which should be moved to
      let find_distinct_product = |variable| {
        debug_assert!(variable < to_decrement_threshold);

        for (i, product) in self.products.iter().enumerate() {
          if product.left == variable {
            return ProductReference::Left { product: i, variable };
          }
          if product.right == variable {
            return ProductReference::Right { product: i, variable };
          }
          if product.variable == variable {
            return ProductReference::Output { product: i, variable };
          }
        }
        panic!("couldn't find distinct product");
      };
      let move_to_left = find_distinct_product(removed.left);
      let move_to_right = find_distinct_product(removed.right);

      // Shift down products
      for product in self.products.iter_mut().skip(key) {
        if (product.left == to_decrement_threshold) || (product.right == to_decrement_threshold) {
          panic!("product used unused product output");
        }

        if product.left > to_decrement_threshold {
          product.left -= 1;
        }
        if product.right > to_decrement_threshold {
          product.right -= 1;
        }
        if product.variable > to_decrement_threshold {
          product.variable -= 1;
        }
      }

      // Shift down constraints
      for constraint in self.constraints.iter_mut() {
        let mut to_remove = vec![];
        let mut weights = vec![];
        for (i, (product_l, weight)) in constraint.WL.clone().drain(..).enumerate() {
          if product_l == key {
            weights.push((move_to_left, weight));
            to_remove.push(i);
          } else if product_l > key {
            constraint.WL[i].0 -= 1;
          }
        }
        assert!(to_remove.len() <= 1);
        for i in to_remove.drain(..) {
          constraint.WL.remove(i);
        }

        for (i, (product_r, weight)) in constraint.WR.clone().drain(..).enumerate() {
          if product_r == key {
            weights.push((move_to_right, weight));
            to_remove.push(i);
          } else if product_r > key {
            constraint.WR[i].0 -= 1;
          }
        }
        assert!(to_remove.len() <= 1);
        for i in to_remove.drain(..) {
          constraint.WR.remove(i);
        }
        for weight in weights.drain(..) {
          constraint.weight(weight.0, weight.1);
        }

        for (product_o, _) in constraint.WO.iter_mut() {
          if *product_o == key {
            panic!("unused output was used in constraint");
          }
          if *product_o > key {
            *product_o -= 1;
          }
        }
      }
    }
  }

  fn remove_empty_constraints(&mut self) {
    let mut offset = 0;
    // TODO: Optimize out this clone
    'constraint: for (i, constraint) in self.constraints.clone().iter().enumerate() {
      let i = i - offset;

      for w in &constraint.WL {
        if w.1 != C::F::ZERO {
          continue 'constraint;
        }
      }
      for w in &constraint.WR {
        if w.1 != C::F::ZERO {
          continue 'constraint;
        }
      }
      for w in &constraint.WO {
        if w.1 != C::F::ZERO {
          continue 'constraint;
        }
      }
      for w in &constraint.WV {
        if w.1 != C::F::ZERO {
          continue 'constraint;
        }
      }
      assert_eq!(constraint.c, C::F::ZERO, "constraint was empty yet had rhs offset");

      self.constraints.remove(i);
      offset += 1;
    }
  }

  // TODO: This can be significantly optimized with post-processing passes
  // TODO: Don't run this on every single prove/verify. It should only be run once at compile time
  fn compile(mut self) -> (ArithmeticCircuitStatement<C>, Option<ArithmeticCircuitWitness<C>>) {
    // Only runs once as we so far don't have value from multiple runs
    for _ in 0 .. 1 {
      // Remove unused products
      self.remove_unused_products();

      // Remove empty constraints
      self.remove_empty_constraints();

      // TODO: Remove duplicate constraints

      // TODO: For a = (x * y) + z, where the x y product only has value to the calculation of a,
      // generate a single constraint for the legitimacy of a
    }

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
            assert_eq!(value.calculate(self.g, self.h), *actual);
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

    (
      ArithmeticCircuitStatement::new(
        self.g,
        self.h,
        self.g_bold1,
        self.g_bold2,
        self.h_bold1,
        self.h_bold2,
        PointVector(V),
        WL,
        WR,
        WO,
        WV,
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
