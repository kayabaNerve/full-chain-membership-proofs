use transcript::Transcript;
use ciphersuite::{group::ff::Field, Ciphersuite};

use ecip::Ecip;
use bulletproofs_plus::{
  arithmetic_circuit::{VariableReference, Constraint, Circuit},
  gadgets::elliptic_curve::EmbeddedCurveOperations,
};

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Permissible<C: Ecip> {
  pub(crate) h: C::G,
  pub(crate) alpha: C::FieldElement,
  pub(crate) beta: C::FieldElement,
}

impl<C: Ecip> Permissible<C> {
  fn u(&self, y: C::FieldElement) -> C::FieldElement {
    (self.alpha * y) + self.beta
  }

  pub(crate) fn elem(&self, y: C::FieldElement) -> bool {
    Option::<C::FieldElement>::from(self.u(y).sqrt()).is_some()
  }

  pub(crate) fn point(&self, point: C::G) -> bool {
    let y = C::to_xy(point).1;
    self.elem(y) && (!self.elem(-y))
  }

  pub(crate) fn make_permissible(&self, mut point: C::G) -> (u64, C::G) {
    let mut offset = 0;
    while !self.point(point) {
      offset += 1;
      point += self.h;
    }
    (offset, point)
  }

  pub(crate) fn gadget<
    T: Transcript,
    C2: Ciphersuite<F = C::FieldElement> + EmbeddedCurveOperations<Embedded = C>,
  >(
    &self,
    circuit: &mut Circuit<T, C2>,
    y: VariableReference,
  ) {
    let sqrt = circuit.add_secret_input(if circuit.prover() {
      Some(
        Option::from(self.u(circuit.unchecked_value(y)).sqrt())
          .expect("proving a y coordinate is permissible despite it not having a sqrt"),
      )
    } else {
      None
    });
    let (l, r, o) = circuit.product(sqrt, sqrt).0;
    circuit.constrain_equality(l, r);

    let mut constraint = Constraint::new("u");
    constraint.weight(circuit.variable_to_product(y).unwrap(), -self.alpha);
    constraint.weight(o, C2::F::ONE);
    constraint.rhs_offset(self.beta);
    circuit.constrain(constraint);
  }
}
