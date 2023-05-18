use rand_core::OsRng;

use transcript::{Transcript, RecommendedTranscript};
use ciphersuite::{
  group::{ff::Field, Group},
  Ciphersuite, Ristretto,
};

use crate::{
  PointVector,
  arithmetic_circuit::{Commitment, Constraint, Circuit},
};

type Generators =
  (PointVector<Ristretto>, PointVector<Ristretto>, PointVector<Ristretto>, PointVector<Ristretto>);

fn generators(n: usize) -> Generators {
  let gens = || {
    let mut res = PointVector::<Ristretto>::new(n);
    for i in 0 .. n {
      res[i] = <Ristretto as Ciphersuite>::G::random(&mut OsRng);
    }
    res
  };
  (gens(), gens(), gens(), gens())
}

#[test]
fn test_point_addition() {
  let (g_bold1, g_bold2, h_bold1, h_bold2) = generators(128);

  let p1 = (x, y, 1);
  let p2 = (x, y);

  let mut transcript = RecommendedTranscript::new(b"Point Addition Circuit Test");

  let mut circuit =
    Circuit::new(g_bold1.clone(), g_bold2.clone(), h_bold1.clone(), h_bold2.clone(), true);
  <C as PointAddition>::add(&mut circuit, p1.0, p1.1, p1.2, p2.0, p2.1);
  let proof = circuit.prove(&mut OsRng, &mut transcript.clone());

  let mut circuit = Circuit::new(g_bold1, g_bold2, h_bold1, h_bold2, false);
  <C as PointAddition>::add(&mut circuit, p1.0, p1.1, p1.2, p2.0, p2.1);
  circuit.verify(&mut transcript, proof);
}
