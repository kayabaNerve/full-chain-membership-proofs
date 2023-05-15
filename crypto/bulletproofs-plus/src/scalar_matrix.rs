use zeroize::{Zeroize, ZeroizeOnDrop};

use transcript::Transcript;

use ciphersuite::{group::ff::PrimeField, Ciphersuite};

use crate::ScalarVector;

// Each vector is considered a row
#[derive(Clone, PartialEq, Eq, Debug, Zeroize, ZeroizeOnDrop)]
pub struct ScalarMatrix<C: Ciphersuite>(pub(crate) Vec<ScalarVector<C>>);

impl<C: Ciphersuite> ScalarMatrix<C> {
  // The first number from the paper's matrix size definitions, the amount of rows
  pub(crate) fn length(&self) -> usize {
    self.0.len()
  }

  // The second number, the length of each row
  pub(crate) fn width(&self) -> usize {
    self.0.get(0).map(|v| v.len()).unwrap_or(0)
  }

  pub(crate) fn mul_vec(&self, vector: &ScalarVector<C>) -> ScalarVector<C> {
    assert_eq!(self.length(), vector.len());
    let mut res = ScalarVector::new(self.width());
    for (row, weight) in self.0.iter().zip(vector.0.iter()) {
      for (i, item) in row.0.iter().enumerate() {
        res[i] += *item * weight;
      }
    }
    assert_eq!(res.len(), self.width());
    res
  }

  pub(crate) fn transcript<T: Transcript>(&self, transcript: &mut T, label: &'static [u8]) {
    // Prevent conflicts between 2x3 and 3x2
    let width = self.width();
    transcript.append_message(b"length", u32::try_from(self.length()).unwrap().to_le_bytes());
    transcript.append_message(b"width", u32::try_from(width).unwrap().to_le_bytes());
    for vector in &self.0 {
      // Make sure this is consistently rectangular
      assert_eq!(vector.len(), width);
      for scalar in &vector.0 {
        transcript.append_message(label, scalar.to_repr());
      }
    }
  }
}
