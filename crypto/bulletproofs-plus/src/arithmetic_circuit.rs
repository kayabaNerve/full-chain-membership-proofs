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

#[derive(Clone, Debug, Zeroize)]
pub struct Constraint<C: BulletproofsCurve> {
  // Each weight (C::F) is bound to a specific variable (usize) to allow post-expansion to valid
  // constraints
  WL: Vec<(usize, C::F)>,
  WR: Vec<(usize, C::F)>,
  WO: Vec<(usize, C::F)>,
  WV: Vec<(usize, C::F)>,
  c: C::F,
}

impl<C: BulletproofsCurve> Constraint<C> {
  pub fn new() -> Self {
    Self { WL: vec![], WR: vec![], WO: vec![], WV: vec![], c: C::F::ZERO }
  }

  pub fn weight_left(&mut self, variable: ProductReference, weight: C::F) -> &mut Self {
    for existing in &self.WL {
      assert!(existing.0 != variable.0);
    }
    self.WL.push((variable.0, weight));
    self
  }
  pub fn weight_right(&mut self, variable: ProductReference, weight: C::F) -> &mut Self {
    for existing in &self.WR {
      assert!(existing.0 != variable.0);
    }
    self.WR.push((variable.0, weight));
    self
  }
  pub fn weight_output(&mut self, variable: ProductReference, weight: C::F) -> &mut Self {
    for existing in &self.WO {
      assert!(existing.0 != variable.0);
    }
    self.WO.push((variable.0, weight));
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
pub struct ProductReference(usize);
#[derive(Copy, Clone, Debug, Zeroize)]
pub struct CommitmentReference(usize);

#[derive(Clone, Debug, Zeroize, ZeroizeOnDrop)]
enum Variable<C: BulletproofsCurve> {
  Secret(Option<C::F>),
  Public(Option<Commitment<C>>, C::G),
  Product(usize, usize, Option<C::F>),
}

impl<C: BulletproofsCurve> Variable<C> {
  fn value(&self) -> Option<C::F> {
    match self {
      Variable::Secret(value) => *value,
      Variable::Public(_, _) => panic!("asked for value of commitment"),
      Variable::Product(_, _, product) => *product,
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
    }
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
  pub fn product(&mut self, a: VariableReference, b: VariableReference) -> ProductReference {
    let left = &self.variables[a.0];
    let right = &self.variables[b.0];
    debug_assert_eq!(left.value().is_some(), right.value().is_some());

    let res = ProductReference(self.products);
    self.products += 1;
    self.variables.push(Variable::Product(
      a.0,
      b.0,
      left.value().map(|left| left * right.value().unwrap()),
    ));
    res
  }

  /// Add a constraint.
  pub fn constrain(&mut self, constraint: Constraint<C>) {
    // TODO: Check commitment weights refer to commitments, W{L, R, O} refer to product terms
    self.constraints.push(constraint);
  }

  // TODO: This can be significantly optimized
  fn compile(self) -> (ArithmeticCircuitStatement<C>, Option<ArithmeticCircuitWitness<C>>) {
    // aL, aR, v, gamma
    let witness = if self.prover {
      let mut variables = HashMap::new();

      let mut aL = vec![];
      let mut aR = vec![];

      let mut v = vec![];
      let mut gamma = vec![];

      for (i, variable) in self.variables.iter().enumerate() {
        match variable {
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
        Variable::Secret(_) => {}
        Variable::Public(_, actual) => V.push(*actual),
        Variable::Product(_, _, _) => n += 1,
      }
    }

    // WL, WR, WO, WV, c
    let mut WL = vec![];
    let mut WR = vec![];
    let mut WO = vec![];
    let mut WV = vec![];
    let mut c = vec![];
    for constraint in self.constraints {
      let mut this_wl = vec![C::F::ZERO; n];
      let mut this_wr = vec![C::F::ZERO; n];
      let mut this_wo = vec![C::F::ZERO; n];
      let mut this_wv = vec![C::F::ZERO; V.len()];

      for wl in constraint.WL {
        this_wl[wl.0] = wl.1;
      }
      for wr in constraint.WR {
        this_wr[wr.0] = wr.1;
      }
      for wo in constraint.WO {
        this_wo[wo.0] = wo.1;
      }
      for wv in constraint.WV {
        this_wv[wv.0] = wv.1;
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
