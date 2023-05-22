use ciphersuite::{group::Group, Ciphersuite};

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
}

impl<C: CurveCycle> Node<C> {
  fn new(even: bool) -> Self {
    Self {
      hash: if even {
        Hash::Even(<C::C1 as Ciphersuite>::G::identity())
      } else {
        Hash::Odd(<C::C2 as Ciphersuite>::G::identity())
      },
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
          next_gens.push(C::c2_hash_to_curve(
            "Curve Tree, Odd Generator",
            &[l_bytes.as_ref(), i.to_le_bytes().as_ref()].concat(),
          ));
        }
        odd_generators.push(next_gens);
      } else {
        let mut next_gens = vec![];
        for i in 0 .. (width_u64 * 2) {
          next_gens.push(C::c1_hash_to_curve(
            "Curve Tree, Even Generator",
            &[l_bytes.as_ref(), i.to_le_bytes().as_ref()].concat(),
          ));
        }
        even_generators.push(next_gens);
      }
    }

    Tree { width, odd_generators, even_generators, node: Node::new(false) }
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
    // TODO: This is O(n). Optimize by having each branch track if it's full
    fn add_to_node<C: CurveCycle>(
      width: usize,
      node: &mut Node<C>,
      leaf: <C::C1 as Ciphersuite>::G,
    ) -> bool {
      if node.children.len() < width {
        node.dirty = true;
        node.children.push(Child::Leaf(leaf));
        return true;
      }

      for child in node.children.iter_mut() {
        match child {
          // No room left on this branch
          Child::Leaf(_) => return false,
          Child::Node(ref mut node) => {
            if add_to_node(width, node, leaf) {
              node.dirty = true;
              return true;
            }
          }
        }
      }

      false
    }

    for leaf in leaves {
      if !add_to_node(self.width, &mut self.node, *leaf) {
        // Clone the current tree for its structure
        let mut sibling = self.node.clone();

        // Reset every field in the clone, removing all leaves
        fn clear<C: CurveCycle>(node: &mut Node<C>) {
          match node.hash {
            Hash::Even(_) => node.hash = Hash::Even(<C::C1 as Ciphersuite>::G::identity()),
            Hash::Odd(_) => node.hash = Hash::Odd(<C::C2 as Ciphersuite>::G::identity()),
          }
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
            assert!(add_to_node(self.width, next, *leaf));
            next.dirty = true;
          }
        }

        self.node = Node {
          hash: if currently_even {
            Hash::Odd(<C::C2 as Ciphersuite>::G::identity())
          } else {
            Hash::Even(<C::C1 as Ciphersuite>::G::identity())
          },
          dirty: true,
          children,
        };
      }
    }
    self.node.dirty = true;

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
}
