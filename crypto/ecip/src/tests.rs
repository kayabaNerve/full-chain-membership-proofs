use rand_core::OsRng;

use ciphersuite::{
  group::{ff::Field, Group},
  Ciphersuite, Pallas, Vesta,
};

use crate::{Ecip, Poly, Divisor};

#[test]
fn test_poly() {
  type F = <Vesta as Ciphersuite>::F;
  let zero = F::ZERO;
  let one = F::ONE;

  {
    let mut poly = Poly::zero();
    poly.y_coefficients = vec![zero, one];

    let mut modulus = Poly::zero();
    modulus.y_coefficients = vec![one];
    assert_eq!(poly.rem(&modulus), Poly::zero());
  }

  {
    let mut poly = Poly::zero();
    poly.y_coefficients = vec![zero, one];

    let mut squared = Poly::zero();
    squared.y_coefficients = vec![zero, zero, zero, one];
    assert_eq!(poly.clone().inner_mul(&poly), squared);
  }

  {
    let mut a = Poly::zero();
    a.zero_coefficient = F::from(2);

    let mut b = Poly::zero();
    b.zero_coefficient = F::from(3);

    let mut res = Poly::zero();
    res.zero_coefficient = F::from(6);
    assert_eq!(a.clone().inner_mul(&b), res);

    b.y_coefficients = vec![F::from(4)];
    res.y_coefficients = vec![F::from(8)];
    assert_eq!(a.clone().inner_mul(&b), res);
    assert_eq!(b.clone().inner_mul(&a), res);

    a.x_coefficients = vec![F::from(5)];
    res.x_coefficients = vec![F::from(15)];
    res.yx_coefficients = vec![vec![F::from(20)]];
    assert_eq!(a.clone().inner_mul(&b), res);
    assert_eq!(b.inner_mul(&a), res);

    // res is now 20xy + 8*y + 15*x + 6
    // res ** 2 =
    //   400*x^2*y^2 + 320*x*y^2 + 64*y^2 + 600*x^2*y + 480*x*y + 96*y + 225*x^2 + 180*x + 36

    let mut squared = Poly::zero();
    squared.y_coefficients = vec![F::from(96), F::from(64)];
    squared.yx_coefficients =
      vec![vec![F::from(480), F::from(600)], vec![F::from(320), F::from(400)]];
    squared.x_coefficients = vec![F::from(180), F::from(225)];
    squared.zero_coefficient = F::from(36);
    assert_eq!(res.clone().inner_mul(&res), squared);
  }
}

#[test]
fn test_divisor() {
  for i in 1 ..= 255 {
    if (i % 2) == 0 {
      continue;
    }
    dbg!(i);

    let mut points = vec![];
    for _ in 0 .. i {
      points.push(<Pallas as Ciphersuite>::G::random(&mut OsRng));
    }
    points.push(-points.iter().sum::<<Pallas as Ciphersuite>::G>());

    let divisor = Divisor::<Pallas>::new(&points);

    let challenge = <Pallas as Ciphersuite>::G::random(&mut OsRng);
    let (x, y) = Pallas::to_xy(challenge);

    let mut rhs = <Vesta as Ciphersuite>::F::ONE;
    for point in points {
      rhs *= x - Pallas::to_xy(point).0;
    }
    assert_eq!(divisor.eval(x, y) * divisor.eval(x, -y), rhs);
  }
}

#[test]
fn test_same_point() {
  let mut points = vec![<Pallas as Ciphersuite>::G::random(&mut OsRng)];
  points.push(points[0]);
  // Pad so there's an even number of points
  points.push(<Pallas as Ciphersuite>::G::random(&mut OsRng));
  points.push(-points.iter().sum::<<Pallas as Ciphersuite>::G>());

  let divisor = Divisor::<Pallas>::new(&points);

  let challenge = <Pallas as Ciphersuite>::G::random(&mut OsRng);
  let (x, y) = Pallas::to_xy(challenge);

  let mut rhs = <Vesta as Ciphersuite>::F::ONE;
  for point in points {
    rhs *= x - Pallas::to_xy(point).0;
  }
  assert_eq!(divisor.eval(x, y) * divisor.eval(x, -y), rhs);
}
