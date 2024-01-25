use rand_core::OsRng;

use transcript::{Transcript, RecommendedTranscript};
use multiexp::{Point as MultiexpPoint};
use ciphersuite::{
  group::{ff::Field, Group},
  Ciphersuite,
};

use bulletproofs_plus::{GeneratorsList, Generators};

use ecip::Ecip;

use crate::{
  CurveCycle,
  tree::{Hash, Tree},
  tests::Pasta,
  pedersen_hash::pedersen_hash_vartime,
  permissible::Permissible,
};

fn check_path(
  tree: &Tree<RecommendedTranscript, Pasta>,
  leaf: <<Pasta as CurveCycle>::C1 as Ciphersuite>::G,
) {
  let path = tree.membership(leaf).unwrap();

  let mut depth = 1;
  let mut curr = Hash::Even(leaf);
  for preimages in path {
    {
      let mut found = false;
      for preimage in &preimages.1 {
        if *preimage == curr {
          found = true;
          break;
        }
      }
      assert!(found);
    }

    let mut even = vec![];
    let mut odd = vec![];
    for preimage in preimages.1 {
      match preimage {
        Hash::Even(hash) => {
          even.push(Pasta::c1_coords(hash).0);
        }
        Hash::Odd(hash) => {
          odd.push(Pasta::c2_coords(hash).0);
        }
      }
    }
    assert!(even.is_empty() ^ odd.is_empty());

    if !even.is_empty() {
      curr = Hash::Odd(
        tree
          .permissible_c2()
          .make_permissible(pedersen_hash_vartime::<<Pasta as CurveCycle>::C2>(
            &even,
            &tree.odd_generators()[.. even.len()],
          ))
          .1,
      );
    } else {
      curr = Hash::Even(
        tree
          .permissible_c1()
          .make_permissible(pedersen_hash_vartime::<<Pasta as CurveCycle>::C1>(
            &odd,
            &tree.even_generators()[.. odd.len()],
          ))
          .1,
      );
    }
    depth += 1;
  }

  assert_eq!(curr, tree.root());
}

#[test]
fn test_tree() {
  let permissible_c1 = Permissible::<<Pasta as CurveCycle>::C1> {
    h: <<Pasta as CurveCycle>::C1 as Ciphersuite>::G::random(&mut OsRng),
    alpha: <<Pasta as CurveCycle>::C1 as Ecip>::FieldElement::random(&mut OsRng),
    beta: <<Pasta as CurveCycle>::C1 as Ecip>::FieldElement::random(&mut OsRng),
  };
  let permissible_c2 = Permissible::<<Pasta as CurveCycle>::C2> {
    h: <<Pasta as CurveCycle>::C2 as Ciphersuite>::G::random(&mut OsRng),
    alpha: <<Pasta as CurveCycle>::C2 as Ecip>::FieldElement::random(&mut OsRng),
    beta: <<Pasta as CurveCycle>::C2 as Ecip>::FieldElement::random(&mut OsRng),
  };
  let leaf_randomness = <<Pasta as CurveCycle>::C1 as Ciphersuite>::G::random(&mut OsRng);

  for width in 2 ..= 4usize {
    let mut even_generators = vec![];
    let mut odd_generators = vec![];
    for _ in 0 .. width {
      even_generators.push(<<Pasta as CurveCycle>::C2 as Ciphersuite>::G::random(&mut OsRng));
      odd_generators.push(<<Pasta as CurveCycle>::C1 as Ciphersuite>::G::random(&mut OsRng));
    }

    let max = u64::try_from(width).unwrap().pow(4);
    let mut tree = Tree::<RecommendedTranscript, Pasta>::new(
      even_generators,
      odd_generators,
      permissible_c1,
      permissible_c2,
      leaf_randomness,
      width,
      max,
    );
    assert_eq!(tree.root(), Hash::Odd(<<Pasta as CurveCycle>::C2 as Ciphersuite>::G::identity()));
    assert_eq!(tree.depth(), 0);

    let mut items = vec![];
    let mut leaves = vec![];
    for _ in 0 .. max {
      items.push(<<Pasta as CurveCycle>::C1 as Ciphersuite>::G::random(&mut OsRng));
      leaves.push(Pasta::c1_coords(*items.last().unwrap()).0);
    }

    for i in 0 .. max {
      let mut new_leaf = items[usize::try_from(i).unwrap()];
      tree.add_leaves(&[new_leaf]);

      // Make the leaf permissible on this end
      while !tree.permissible_c1().point(items[usize::try_from(i).unwrap()]) {
        items[usize::try_from(i).unwrap()] += leaf_randomness;
        leaves[usize::try_from(i).unwrap()] =
          Pasta::c1_coords(items[usize::try_from(i).unwrap()]).0;
        new_leaf = items[usize::try_from(i).unwrap()];
      }

      let i = i + 1;
      let mut pow = 1;
      while u64::try_from(width).unwrap().pow(pow) < i {
        pow += 1;
      }
      let depth = usize::try_from(pow).unwrap();
      assert_eq!(tree.depth(), depth);

      let mut even = leaves[.. usize::try_from(i).unwrap()].to_vec();
      let mut odd = vec![];
      fn hash<T: 'static + Transcript, C: Ecip>(
        generators: &[C::G],
        permissible: &Permissible<C>,
        width: usize,
        values: &mut Vec<C::F>,
      ) -> Vec<C::G> {
        let mut res = vec![];
        while !values.is_empty() {
          let mut these = vec![];
          while (these.len() < width) && (!values.is_empty()) {
            these.push(values.remove(0));
          }
          res.push(
            permissible
              .make_permissible(pedersen_hash_vartime::<C>(&these, &generators[.. these.len()]))
              .1,
          );
        }
        res
      }

      let mut last_even = None;
      let mut last_odd = None;
      for i in 1 ..= depth {
        if !even.is_empty() {
          let hashes = hash::<RecommendedTranscript, <Pasta as CurveCycle>::C2>(
            tree.odd_generators(),
            &permissible_c2,
            width,
            &mut even,
          );
          for hash in hashes {
            last_odd = Some(hash);
            odd.push(Pasta::c2_coords(hash).0);
          }
        } else {
          let hashes = hash::<RecommendedTranscript, <Pasta as CurveCycle>::C1>(
            tree.even_generators(),
            &permissible_c1,
            width,
            &mut odd,
          );
          for hash in hashes {
            last_even = Some(hash);
            even.push(Pasta::c1_coords(hash).0);
          }
        }
      }

      if (depth % 2) == 0 {
        assert_eq!(tree.root(), Hash::Even(last_even.unwrap()));
        assert_eq!(even.remove(0), Pasta::c1_coords(last_even.unwrap()).0);
      } else {
        assert_eq!(tree.root(), Hash::Odd(last_odd.unwrap()));
        assert_eq!(odd.remove(0), Pasta::c2_coords(last_odd.unwrap()).0);
      }
      assert!(even.is_empty());
      assert!(odd.is_empty());

      check_path(&tree, new_leaf);
    }

    for leaf in items {
      check_path(&tree, leaf);
    }
  }
}
