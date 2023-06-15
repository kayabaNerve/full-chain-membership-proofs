use core::fmt::Debug;
use std::collections::HashMap;

use transcript::Transcript;
use ciphersuite::{
  group::{
    ff::{Field, PrimeField},
    Group, GroupEncoding,
  },
  Ciphersuite,
};

use ecip::Ecip;
use bulletproofs_plus::{VectorCommitmentGenerators, Generators};

use crate::{CurveCycle, permissible::Permissible};

#[derive(Clone, PartialEq, Eq, Debug)]
enum Child<C: CurveCycle> {
  Leaf(<C::C1 as Ciphersuite>::G),
  Node(Node<C>),
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Hash<C: CurveCycle> {
  Even(<C::C1 as Ciphersuite>::G),
  Odd(<C::C2 as Ciphersuite>::G),
}

#[derive(Clone, PartialEq, Eq, Debug)]
struct Node<C: CurveCycle> {
  permissibility_offset: u64,
  hash: Hash<C>,
  full: bool,
  dirty: bool,
  children: Vec<Child<C>>,
}

// Structured as having all of its branches filled out, even ones not in use, yet only active
// leaves
// When the tree reaches capacity, it has a parent node added, growing its capacity
#[derive(Clone, Debug)]
pub struct Tree<T: Transcript, C: CurveCycle>
where
  T::Challenge: Debug,
{
  permissible_c1: Permissible<C::C1>,
  permissible_c2: Permissible<C::C2>,
  leaf_randomness: <C::C1 as Ciphersuite>::G,

  width: usize,
  odd_generators: Vec<VectorCommitmentGenerators<T, C::C2>>,
  even_generators: Vec<VectorCommitmentGenerators<T, C::C1>>,

  parameters_hash: T::Challenge,

  node: Node<C>,

  // Map of leaf to path, where path is:
  // 1) Short. All missing path elements (due to tree growth) are implicitly the left-most.
  // 2) Only to the bottom branch, not to the leaf on the bottom branch.
  paths: HashMap<Vec<u8>, Vec<usize>>,
}

impl<C: CurveCycle> Node<C> {
  fn new(even: bool) -> Self {
    Self {
      permissibility_offset: 0,
      hash: if even {
        Hash::Even(<C::C1 as Ciphersuite>::G::identity())
      } else {
        Hash::Odd(<C::C2 as Ciphersuite>::G::identity())
      },
      full: false,
      dirty: false,
      children: vec![],
    }
  }
}

fn depth<C: CurveCycle>(node: &Node<C>) -> usize {
  let children = &node.children;
  if children.is_empty() {
    return 0;
  }

  match &children[0] {
    Child::Leaf(_) => 1,
    Child::Node(node) => depth(node) + 1,
  }
}

impl<T: Transcript, C: CurveCycle> Tree<T, C>
where
  T::Challenge: Debug,
{
  pub fn new(
    permissible_c1: Permissible<C::C1>,
    permissible_c2: Permissible<C::C2>,
    leaf_randomness: <C::C1 as Ciphersuite>::G,
    width: usize,
    max_size: u64,
  ) -> Self {
    assert!(width >= 2);

    let width_u64 = u64::try_from(width).unwrap();
    let mut pow = 1;
    while width_u64.pow(pow) < max_size {
      pow += 1;
    }

    let mut transcript = T::new(b"Curve Trees Parameters");
    transcript.domain_separate(b"parameters");
    transcript.append_message(b"permissible_c1_alpha", permissible_c1.alpha.to_repr());
    transcript.append_message(b"permissible_c1_beta", permissible_c1.beta.to_repr());
    transcript.append_message(b"permissible_c2_alpha", permissible_c2.alpha.to_repr());
    transcript.append_message(b"permissible_c2_beta", permissible_c2.beta.to_repr());
    transcript.append_message(b"leaf_randomness", leaf_randomness.to_bytes());
    transcript.append_message(b"width", width_u64.to_le_bytes());

    // pow now represents the amount of layers we need generators for
    // TODO: Table these?
    let mut odd_generators = vec![];
    let mut even_generators = vec![];
    for l in 1 ..= pow {
      let l_bytes = l.to_le_bytes();
      if (l % 2) == 1 {
        let mut next_gens = vec![];
        for i in 0 .. width_u64 {
          next_gens.push(<C::C2 as Ecip>::hash_to_G(
            "Curve Tree, Odd Generator",
            &[l_bytes.as_ref(), i.to_le_bytes().as_ref()].concat(),
          ));
        }
        odd_generators.push(VectorCommitmentGenerators::new(&next_gens));
      } else {
        let mut next_gens = vec![];
        for i in 0 .. width_u64 {
          next_gens.push(<C::C1 as Ecip>::hash_to_G(
            "Curve Tree, Even Generator",
            &[l_bytes.as_ref(), i.to_le_bytes().as_ref()].concat(),
          ));
        }
        even_generators.push(VectorCommitmentGenerators::new(&next_gens));
      }
    }

    transcript.domain_separate(b"even_generators");
    for even_generators in &even_generators {
      transcript.append_message(b"transcript", even_generators.transcript());
    }
    for odd_generators in &odd_generators {
      transcript.append_message(b"transcript", odd_generators.transcript());
    }

    Tree {
      permissible_c1,
      permissible_c2,
      leaf_randomness,

      width,
      odd_generators,
      even_generators,

      parameters_hash: transcript.challenge(b"summary"),

      node: Node::new(false),
      paths: HashMap::new(),
    }
  }

  pub fn parameters_hash(&self) -> &T::Challenge {
    &self.parameters_hash
  }

  pub fn whitelist_vector_commitments(
    &self,
    c1: &mut Generators<T, C::C1>,
    c2: &mut Generators<T, C::C2>,
  ) {
    for odd_generators in &self.odd_generators {
      c2.whitelist_vector_commitments(b"Curve Tree, Odd Generators", odd_generators);
    }
    for even_generators in &self.even_generators {
      c1.whitelist_vector_commitments(b"Curve Tree, Even Generators", even_generators);
    }
  }

  pub(crate) fn permissible_c1(&self) -> &Permissible<C::C1> {
    &self.permissible_c1
  }
  pub(crate) fn permissible_c2(&self) -> &Permissible<C::C2> {
    &self.permissible_c2
  }

  pub fn width(&self) -> usize {
    self.width
  }

  pub fn depth(&self) -> usize {
    depth(&self.node)
  }

  pub fn root(&self) -> Hash<C> {
    assert!(!self.node.dirty);
    self.node.hash
  }

  pub fn even_generators(&self, layer: usize) -> Option<&VectorCommitmentGenerators<T, C::C1>> {
    if (layer % 2) != 0 {
      return None;
    }
    if layer < 2 {
      return None;
    }
    self.even_generators.get((layer - 2) / 2)
  }
  pub fn odd_generators(&self, layer: usize) -> Option<&VectorCommitmentGenerators<T, C::C2>> {
    if (layer % 2) != 1 {
      return None;
    }
    self.odd_generators.get(layer / 2)
  }

  pub fn add_leaves(&mut self, leaves: &[<C::C1 as Ciphersuite>::G]) {
    fn add_to_node<C: CurveCycle>(
      width: usize,
      node: &mut Node<C>,
      leaf: <C::C1 as Ciphersuite>::G,
    ) -> (bool, Option<Vec<usize>>) {
      if node.full {
        return (true, None);
      }

      // If this node has room, add it
      if node.children.len() < width {
        node.dirty = true;
        node.children.push(Child::Leaf(leaf));
        node.full = node.children.len() == width;
        return (node.full, Some(vec![]));
      }

      for (c, child) in node.children.iter_mut().enumerate() {
        match child {
          Child::Leaf(_) => panic!("full leaf wasn't flagged as full"),
          Child::Node(ref mut child) => {
            let (full_child, path) = add_to_node(width, child, leaf);
            if let Some(mut path) = path {
              if full_child {
                node.full = c == (width - 1);
              }
              node.dirty = true;
              path.push(c);
              return (node.full, Some(path));
            }
          }
        }
      }

      (node.full, None)
    }

    for leaf in leaves {
      // Make the leaf permissible
      let mut leaf = *leaf;
      while !self.permissible_c1.point(leaf) {
        leaf += self.leaf_randomness;
      }

      // Only allow leaves to be added once
      // While leaves may legitimately appear multiple times, any one insertion allows proving
      // membership
      if self.paths.contains_key(leaf.to_bytes().as_ref()) {
        continue;
      }

      // Ban identity to obtain certain properties in-circuit
      if leaf.is_identity().into() {
        continue;
      }

      let (full, mut path) = add_to_node(self.width, &mut self.node, leaf);
      if path.is_none() {
        assert!(full);

        // Clone the current tree for its structure
        let mut sibling = self.node.clone();

        // Reset every field in the clone, removing all leaves
        fn clear<C: CurveCycle>(node: &mut Node<C>) {
          match node.hash {
            Hash::Even(_) => node.hash = Hash::Even(<C::C1 as Ciphersuite>::G::identity()),
            Hash::Odd(_) => node.hash = Hash::Odd(<C::C2 as Ciphersuite>::G::identity()),
          }
          node.full = false;
          node.dirty = false;

          match &node.children[0] {
            Child::Leaf(_) => {
              node.children.truncate(0);
              return;
            }
            Child::Node(_) => {}
          }

          for child in node.children.iter_mut() {
            match child {
              Child::Leaf(_) => panic!("leaf on branch where child[0] wasn't a leaf"),
              Child::Node(ref mut node) => clear(node),
            }
          }
        }
        clear(&mut sibling);

        let currently_even = matches!(self.node.hash, Hash::Even(_));

        let mut children = vec![Child::Node(sibling); self.width - 1];
        children.insert(0, Child::Node(self.node.clone()));
        match children[1] {
          Child::Leaf(_) => panic!("leaf on newly grown tree's top node"),
          Child::Node(ref mut next) => {
            let (full, mut new_path) = add_to_node(self.width, next, leaf);
            assert!(!full);
            new_path.as_mut().unwrap().push(1);
            path = new_path;
          }
        }

        self.node = Node {
          permissibility_offset: 0,
          hash: if currently_even {
            Hash::Odd(<C::C2 as Ciphersuite>::G::identity())
          } else {
            Hash::Even(<C::C1 as Ciphersuite>::G::identity())
          },
          full: false,
          dirty: true,
          children,
        };
      }

      self.paths.insert(leaf.to_bytes().as_ref().to_vec(), path.unwrap());
    }

    fn clean<T: Transcript, C: CurveCycle>(
      permissible_c1: &Permissible<C::C1>,
      permissible_c2: &Permissible<C::C2>,
      odd_generators: &[VectorCommitmentGenerators<T, C::C2>],
      even_generators: &[VectorCommitmentGenerators<T, C::C1>],
      node: &mut Node<C>,
    ) {
      if !node.dirty {
        return;
      }

      let mut child_hashes = vec![];
      for child in node.children.iter_mut() {
        match child {
          Child::Leaf(leaf) => child_hashes.push(Hash::Even(*leaf)),
          Child::Node(ref mut node) => {
            clean(permissible_c1, permissible_c2, odd_generators, even_generators, node);
            child_hashes.push(node.hash);
          }
        }
      }

      let mut even_elems = vec![];
      let mut odd_elems = vec![];
      for hash in child_hashes {
        match hash {
          Hash::Even(hash) => {
            assert!(matches!(node.hash, Hash::Odd(_)));
            even_elems.push(C::c1_coords(hash).0);
          }
          Hash::Odd(hash) => {
            assert!(matches!(node.hash, Hash::Even(_)));
            odd_elems.push(C::c2_coords(hash).0);
          }
        }
      }

      let this_node_depth = depth(node);
      node.permissibility_offset = match &mut node.hash {
        Hash::Even(ref mut hash) => {
          assert!(even_elems.is_empty());
          assert_eq!(this_node_depth % 2, 0);
          // Even generators are 2, 4, 6
          let even_generators = &even_generators[(this_node_depth - 2) / 2];
          while odd_elems.len() < even_generators.len() {
            odd_elems.push(<C::C1 as Ciphersuite>::F::ZERO);
          }
          let permissioned =
            permissible_c1.make_permissible(even_generators.commit_vartime(&odd_elems));
          *hash = permissioned.1;
          permissioned.0
        }
        Hash::Odd(ref mut hash) => {
          assert!(odd_elems.is_empty());
          assert_eq!(this_node_depth % 2, 1);
          // Truncating division
          let odd_generators = &odd_generators[this_node_depth / 2];
          while even_elems.len() < odd_generators.len() {
            even_elems.push(<C::C2 as Ciphersuite>::F::ZERO);
          }
          let permissioned =
            permissible_c2.make_permissible(odd_generators.commit_vartime(&even_elems));
          *hash = permissioned.1;
          permissioned.0
        }
      };
      node.dirty = false;
    }
    clean(
      &self.permissible_c1,
      &self.permissible_c2,
      &self.odd_generators,
      &self.even_generators,
      &mut self.node,
    );
  }

  // Return the complimentary preimages for the specified leaf.
  pub fn membership(&self, leaf: <C::C1 as Ciphersuite>::G) -> Option<Vec<(u64, Vec<Hash<C>>)>> {
    let mut path = self.paths.get(leaf.to_bytes().as_ref()).cloned()?;

    // The path length should be the depth - 1
    // If the tree has since grown, the path will be short, yet the missing elements will
    // always be the left-most ones
    while path.len() < (self.depth() - 1) {
      path.push(0);
    }

    let mut res = vec![];
    let mut curr = &self.node;
    while let Some(child) = path.pop() {
      // Get the hashes of all children for this node
      let mut preimages = vec![];
      for child in &curr.children {
        match child {
          Child::Leaf(_) => panic!("path has elements yet no further children exist"),
          Child::Node(node) => preimages.push(node.hash),
        }
      }

      res.push((curr.permissibility_offset, preimages));

      // Update curr
      curr = match &curr.children[child] {
        Child::Leaf(_) => unreachable!(),
        Child::Node(node) => node,
      };
    }

    let mut preimages = vec![];
    for child in &curr.children {
      match child {
        Child::Leaf(leaf) => preimages.push(Hash::Even(*leaf)),
        Child::Node(_) => panic!("path is out of elements yet node has further children"),
      }
    }

    {
      let mut found = false;
      for preimage in &preimages {
        if *preimage == Hash::Even(leaf) {
          found = true;
          break;
        }
      }
      assert!(found);
    }

    res.push((curr.permissibility_offset, preimages));

    res.reverse();
    Some(res)
  }
}
