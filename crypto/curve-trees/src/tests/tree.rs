use rand_core::OsRng;

use ciphersuite::{group::Group, Ciphersuite};

use crate::{
  CurveCycle,
  tree::{Hash, Tree},
  tests::Pasta,
  pedersen_hash::pedersen_hash_vartime,
};

#[test]
fn test_tree() {
  for width in 2 ..= 4usize {
    let max = u64::try_from(width).unwrap().pow(4);
    let mut tree = Tree::<Pasta>::new(width, max);
    assert_eq!(tree.root(), Hash::Odd(<<Pasta as CurveCycle>::C2 as Ciphersuite>::G::identity()));
    assert_eq!(tree.depth(), 0);

    assert!(tree.odd_generators(0).is_none());
    assert!(tree.even_generators(0).is_none());
    for i in 1 ..= 4 {
      if (i % 2) == 0 {
        assert!(tree.even_generators(i).is_some());
        assert!(tree.odd_generators(i).is_none());
      } else {
        assert!(tree.even_generators(i).is_none());
        assert!(tree.odd_generators(i).is_some());
      }
    }
    for i in 5 ..= 8 {
      assert!(tree.odd_generators(i).is_none());
      assert!(tree.even_generators(i).is_none());
    }

    let mut items = vec![];
    let mut leaves = vec![];
    for _ in 0 .. max {
      items.push(<<Pasta as CurveCycle>::C1 as Ciphersuite>::G::random(&mut OsRng));
      let coords = Pasta::c1_coords(*items.last().unwrap());
      leaves.push(coords.0);
      leaves.push(coords.1);
    }

    for i in 0 .. max {
      tree.add_leaves(&[items[usize::try_from(i).unwrap()]]);

      let i = i + 1;
      let mut pow = 1;
      while u64::try_from(width).unwrap().pow(pow) < i {
        pow += 1;
      }
      let depth = usize::try_from(pow).unwrap();
      assert_eq!(tree.depth(), depth);

      let mut even = leaves[.. (usize::try_from(i).unwrap() * 2)].to_vec();
      let mut odd = vec![];
      fn hash<C: Ciphersuite>(
        width: usize,
        values: &mut Vec<C::F>,
        generators: &[C::G],
      ) -> Vec<C::G> {
        let mut res = vec![];
        while !values.is_empty() {
          let mut these = vec![];
          while (these.len() < (width * 2)) && (!values.is_empty()) {
            these.push(values.remove(0));
          }
          res.push(pedersen_hash_vartime::<C>(&these, &generators[.. these.len()]));
        }
        res
      }

      let mut last_even = None;
      let mut last_odd = None;
      for i in 1 ..= depth {
        if !even.is_empty() {
          let hashes =
            hash::<<Pasta as CurveCycle>::C2>(width, &mut even, tree.odd_generators(i).unwrap());
          for hash in hashes {
            last_odd = Some(hash);
            let coords = Pasta::c2_coords(hash);
            odd.push(coords.0);
            odd.push(coords.1);
          }
        } else {
          let hashes =
            hash::<<Pasta as CurveCycle>::C1>(width, &mut odd, tree.even_generators(i).unwrap());
          for hash in hashes {
            last_even = Some(hash);
            let coords = Pasta::c1_coords(hash);
            even.push(coords.0);
            even.push(coords.1);
          }
        }
      }

      if (depth % 2) == 0 {
        assert_eq!(tree.root(), Hash::Even(last_even.unwrap()));
        let coords = Pasta::c1_coords(last_even.unwrap());
        assert_eq!(even.remove(0), coords.0);
        assert_eq!(even.remove(0), coords.1);
      } else {
        assert_eq!(tree.root(), Hash::Odd(last_odd.unwrap()));
        let coords = Pasta::c2_coords(last_odd.unwrap());
        assert_eq!(odd.remove(0), coords.0);
        assert_eq!(odd.remove(0), coords.1);
      }
      assert!(even.is_empty());
      assert!(odd.is_empty());
    }
  }
}
