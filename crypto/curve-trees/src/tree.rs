use std::collections::HashMap;

use ciphersuite::{
  group::{Group, GroupEncoding},
  Ciphersuite,
};

use ecip::Ecip;

use crate::{CurveCycle, pedersen_hash::pedersen_hash_vartime};

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
  hash: Hash<C>,
  full: bool,
  dirty: bool,
  children: Vec<Child<C>>,
}

// Structured as having all of its branches filled out, even ones not in use, yet only active
// leaves
// When the tree reaches capacity, it has a parent node added, growing its capacity
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Tree<C: CurveCycle> {
  width: usize,
  odd_generators: Vec<Vec<<C::C2 as Ciphersuite>::G>>,
  even_generators: Vec<Vec<<C::C1 as Ciphersuite>::G>>,

  node: Node<C>,

  // Map of leaf to path, where path is:
  // 1) Short. All missing path elements (due to tree growth) are implicitly the left-most.
  // 2) Only to the bottom branch, not to the leaf on the bottom branch.
  paths: HashMap<Vec<u8>, Vec<usize>>,
}

impl<C: CurveCycle> Node<C> {
  fn new(even: bool) -> Self {
    Self {
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

impl<C: CurveCycle> Tree<C> {
  pub fn new(width: usize, max_size: u64) -> Self {
    assert!(width >= 2);

    let width_u64 = u64::try_from(width).unwrap();
    let mut pow = 1;
    while width_u64.pow(pow) < max_size {
      pow += 1;
    }

    // pow now represents the amount of layers we need generators for
    // TODO: Table these?
    let mut odd_generators = vec![];
    let mut even_generators = vec![];
    for l in 1 ..= pow {
      let l_bytes = l.to_le_bytes();
      if (l % 2) == 1 {
        let mut next_gens = vec![];
        for i in 0 .. (width_u64 * 2) {
          next_gens.push(<C::C2 as Ecip>::hash_to_G(
            "Curve Tree, Odd Generator",
            &[l_bytes.as_ref(), i.to_le_bytes().as_ref()].concat(),
          ));
        }
        odd_generators.push(next_gens);
      } else {
        let mut next_gens = vec![];
        for i in 0 .. (width_u64 * 2) {
          next_gens.push(<C::C1 as Ecip>::hash_to_G(
            "Curve Tree, Even Generator",
            &[l_bytes.as_ref(), i.to_le_bytes().as_ref()].concat(),
          ));
        }
        even_generators.push(next_gens);
      }
    }

    Tree { width, odd_generators, even_generators, node: Node::new(false), paths: HashMap::new() }
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

  pub fn even_generators(&self, layer: usize) -> Option<&[<C::C1 as Ciphersuite>::G]> {
    if (layer % 2) != 0 {
      return None;
    }
    if layer < 2 {
      return None;
    }
    self.even_generators.get((layer - 2) / 2).map(AsRef::as_ref)
  }
  pub fn odd_generators(&self, layer: usize) -> Option<&[<C::C2 as Ciphersuite>::G]> {
    if (layer % 2) != 1 {
      return None;
    }
    self.odd_generators.get(layer / 2).map(AsRef::as_ref)
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

      let (full, mut path) = add_to_node(self.width, &mut self.node, *leaf);
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
            let (full, mut new_path) = add_to_node(self.width, next, *leaf);
            assert!(!full);
            new_path.as_mut().unwrap().push(1);
            path = new_path;
          }
        }

        self.node = Node {
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

    fn clean<C: CurveCycle>(
      odd_generators: &[Vec<<C::C2 as Ciphersuite>::G>],
      even_generators: &[Vec<<C::C1 as Ciphersuite>::G>],
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
            clean(odd_generators, even_generators, node);
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
            // TODO: The curve trees paper describes a single coordinate optimization
            let (x, y) = C::c1_coords(hash);
            even_elems.push(x);
            even_elems.push(y);
          }
          Hash::Odd(hash) => {
            assert!(matches!(node.hash, Hash::Even(_)));
            let (x, y) = C::c2_coords(hash);
            odd_elems.push(x);
            odd_elems.push(y);
          }
        }
      }

      let this_node_depth = depth(node);
      match &mut node.hash {
        Hash::Even(ref mut hash) => {
          assert!(even_elems.is_empty());
          assert_eq!(this_node_depth % 2, 0);
          *hash = pedersen_hash_vartime::<C::C1>(
            &odd_elems,
            // Even generators are 2, 4, 6
            &even_generators[(this_node_depth - 2) / 2][.. odd_elems.len()],
          );
        }
        Hash::Odd(ref mut hash) => {
          assert!(odd_elems.is_empty());
          assert_eq!(this_node_depth % 2, 1);
          *hash = pedersen_hash_vartime::<C::C2>(
            &even_elems,
            // Truncating division
            &odd_generators[this_node_depth / 2][.. even_elems.len()],
          );
        }
      }
      node.dirty = false;
    }
    clean(&self.odd_generators, &self.even_generators, &mut self.node);
  }

  // Return the complimentary preimages for the specified leaf.
  pub fn membership(&self, leaf: <C::C1 as Ciphersuite>::G) -> Option<Vec<Vec<Hash<C>>>> {
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

      // Update curr
      curr = match &curr.children[child] {
        Child::Leaf(_) => unreachable!(),
        Child::Node(node) => node,
      };

      res.push(preimages);
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

    res.push(preimages);

    res.reverse();
    Some(res)
  }
}
