#[crate_id = "rbtree"];
#[feature(asm)];

extern mod extra;

#[inline]
#[cfg(target_arch = "x86_64")] #[cfg(target_arch = "x86")]
// yeah, yeah i know...
fn m_depth(n: uint) -> uint {
  unsafe {
    let mut ret: uint;
    asm!("bsr $1, $0" : "=r"(ret) : "r"(n) :: "volatile");
    return ret+1;
  }
}

#[inline]
fn ptr_eq<T>(t1: &T, t2: &T) -> bool {
  std::ptr::to_unsafe_ptr(t1) == std::ptr::to_unsafe_ptr(t2)
}

#[deriving(Eq)]
enum Color {
  Red,
  Black,
}

#[deriving(Eq)]
enum Child {
  Left,
  Right,
}

struct Node<K, V> {
  color: Color,
  data: V,
  key: K,
  left: Option<~Node<K, V>>,
  right: Option<~Node<K, V>>,
}

trait Colored<K, V> {
  fn color(&self) -> Color;
  fn paint(&mut self, Color) -> bool;
  fn insert(&mut self, key: K, value: V) -> Option<V>;
  fn pop(&mut self, key: &K) -> Option<V>;
  fn popMin(&mut self) -> ~Node<K, V>;
}

impl<K: Ord, V> Colored<K, V> for Option<~Node<K, V>> {
  #[inline(always)]
  fn color(&self) -> Color {
    self.as_ref().map_or(Black, |n| n.color)
  }

  // Returns true if the node could be painted.
  #[inline(always)]
  fn paint(&mut self, c: Color) -> bool {
    self.as_mut().map_or(false, |n| {n.color = c; true})
  }

  fn insert(&mut self, key: K, val: V) -> Option<V> {
    match self {
      &None => {
        *self = Some(~Node::new(key, val));
        None
      }
      &Some(ref mut node) => {
        if node.left.color() == Red && node.right.color() == Red {
          node.color_flip_black();
        }
        let ret = node.insert(key, val);
        node.fix();
        ret
      }
    }
  }

  // Fails if self is none.
  fn popMin(&mut self) -> ~Node<K, V> {
    if self.as_mut().unwrap().left.is_none() {
      self.take().unwrap()
    } else {
      let node = self.as_mut().unwrap();
      if node.left.color() == Red &&
         node.left.as_ref().map_or(Black, |n| n.left.color()) == Black {
        node.moveRedLeft();
      }
      let ret = node.left.popMin();
      node.fix();
      ret
    }
  }

  fn pop(&mut self, key: &K) -> Option<V> {
    match self {
      &None => return None,
      &Some(_) => {
        if *key < self.as_ref().unwrap().key {
          let node = self.as_mut().unwrap();
          if node.left.color() == Red &&
             node.left.as_ref().map_or(Black, |n| n.left.color()) == Red {
            node.moveRedLeft();
          }
          let ret = node.left.pop(key);
          node.fix();
          return ret;
        }
        if self.as_ref().unwrap().left.color() == Red {
          self.as_mut().unwrap().rrotate();
        }
        if !(*key > self.as_ref().unwrap().key) &&
           self.as_ref().unwrap().right.is_none() {
          return self.take().map(|n| n.data);
        }
        {
          let node  = self.as_mut().unwrap();
          if node.right.color() == Black &&
             node.right.as_ref().map_or(Black, |n| n.left.color()) == Black {
            node.moveRedRight();
          }
          if *key > node.key {
            let ret = node.right.pop(key);
            node.fix();
            return ret;
          }
        }
        let mut min = self.as_mut().unwrap().right.popMin();
        let ~Node {left: l, right: r, color: c, data: d, key: _} = self.take().unwrap();
        min.left = l;
        min.right = r;
        min.color = c;
        *self = Some(min);
        self.as_mut().unwrap().fix();
        return Some(d);
      }
    }
  }
}

trait NodeRef {
  fn moveRedLeft(&mut self);
  fn moveRedRight(&mut self);
  fn lrotate(&mut self)  -> bool;
  fn rrotate(&mut self) -> bool;
  fn fix(&mut self);
}

impl<K: Ord, V> NodeRef for ~Node<K, V> {
  fn moveRedLeft(&mut self) {
    self.color_flip();
    if self.right.as_ref().map_or(false, |n| n.left.color() == Red) {
      self.right.as_mut().unwrap().rrotate();
      self.lrotate();
      self.color_flip();
    }
  }

  fn moveRedRight(&mut self) {
    self.color_flip();
    if self.left.as_ref().map_or(false, |n| n.left.color() == Red) {
      self.rrotate();
      self.color_flip();
    }
  }

  #[inline(always)]
  fn lrotate(&mut self)  -> bool {
    // Rotation of the root
    let mut y = match self.right.take() {
      None => return false, Some(_y) => _y
    };

    std::util::swap(self, &mut y);
    std::util::swap(&mut y.right, &mut self.left);
    self.color = y.color;
    y.color = Red;
    self.left = Some(y);
    true
  }

  #[inline(always)]
  fn rrotate(&mut self) -> bool {
    let mut y = match self.left.take() {
      None => return false, Some(_y) => _y
    };

    std::util::swap(self, &mut y);
    std::util::swap(&mut y.left, &mut self.right);
    self.color = y.color;
    y.color = Red;
    self.right = Some(y);
    true
  }

  fn fix(&mut self) {
    if self.right.color() == Red && self.left.color() == Black {
      self.lrotate();
    } else if self.left.color() == Red &&
              self.left.as_ref().map_or(Black, |n| n.left.color()) == Red {
      self.rrotate();
    }
  }
}

impl<K: Ord, V> Node<K, V> {
  #[inline]
  fn new(key: K, val: V) -> Node<K, V> {
    Node {
      color: Red, data: val, key: key, left: None, right: None,
    }
  }

  #[inline]
  fn color_flip_black(&mut self) {
    // This is a 4-node, split it to make sure the search does not
    // terminate on a 4-node.
    self.color = Red;
    self.left.paint(Black);
    self.right.paint(Black);
  }

  #[inline]
  fn color_flip(&mut self) {
    if self.color == Red {
      self.color = Black;
      self.left.paint(Red);
      self.right.paint(Red);
    } else {
      self.color_flip_black()
    }
  }

  fn find_mut<'a>(&'a mut self, key: &K) -> Option<&'a mut V> {
    match if key < &self.key {
      self.left.as_mut()
    } else if key > &self.key {
      self.right.as_mut()
    } else {
      return Some(&mut self.data);
    } {
      Some(node) => return node.find_mut(key),
      None => None,
    }
  }

  fn find<'a>(&'a self, key: &K) -> Option<&'a V> {
    match if key < &self.key {
      self.left.as_ref()
    } else if key > &self.key {
      self.right.as_ref()
    } else {
      return Some(&self.data);
    } {
      Some(node) => return node.find(key),
      None => None,
    }
  }

  #[inline(always)]
  fn insert(&mut self, key: K, mut val: V) -> Option<V> {
    if key < self.key {
      self.left.insert(key, val)
    } else if key > self.key {
      self.right.insert(key, val)
    } else {
      std::util::swap(&mut self.data, &mut val);
      Some(val)
    }
  }

  fn print(&self) {
    print!("{:?}({:?}) -> ", self.color, self.data);
    self.left.as_ref().map(|n| print!("{:?}({:?}) , ", n.color, n.data));
    self.right.as_ref().map(|n| print!(" , {:?}({:?})", n.color, n.data));
    print!("\n");
    self.left.as_ref().map(|n| n.print());
    self.right.as_ref().map(|n| n.print());
    print!("\n");
  }

}

impl<K: Ord, V: Eq> Eq for Node<K, V> {
  fn eq(&self, other: &Node<K, V>) -> bool {
    self.key <= other.key && self.key >= other.key &&
      self.data == other.data &&
      self.left == other.left &&
      self.right == other.right
  }
}

pub struct RbTree<K, V> {
  root: Option<~Node<K, V>>,
  len: uint,
}

impl<K: Ord, V> RbTree<K, V> {
  /// Creates a new red-black tree.
  pub fn new() -> RbTree<K, V> {
    RbTree {
      root: None, len: 0,
    }
  }

  /// Insert a key-value pair in the tree and return true,
  /// or do nothing and return false if the key is already present.
  pub fn insert(&mut self, key: K, val: V) -> Option<V> {
    let ret = self.root.insert(key, val).or_else(|| {
      self.len += 1;
      None
    });
    self.root.paint(Black);
    ret
  }

  pub fn iter<'a>(&'a self) -> RbTreeIterator<'a, K, V> {
    let mut iter = RbTreeIterator { stack: std::vec::with_capacity(m_depth(self.len)) };
    iter.push_left_tree(self.root.as_ref());
    iter
  }

}

impl<K: Ord+Eq, V: Eq> RbTree<K, V> {
  /// Returns true only if both tree are identical, unlike eq()
  /// wich returns true if both tree contain the same values, even
  /// if they are aranged in a different ways in each tree.
  pub fn exact_eq(&self, other: &RbTree<K, V>) -> bool {
    self.len == other.len && self.root == other.root
  }
}

impl<K, V> Container for RbTree<K, V> {
  fn len(&self) -> uint {
    self.len
  }
}

impl<K, V> Mutable for RbTree<K, V> {
  fn clear(&mut self) {
    self.root.take();
    self.len = 0;
  }
}

impl<K: Ord+Eq, V: Eq> Eq for RbTree<K, V> {
  /// Returns true if both tree contain the same values.
  fn eq(&self, other: &RbTree<K, V>) -> bool {
    self.len == other.len && self.iter().to_owned_vec() == other.iter().to_owned_vec()
  }
}

impl<K: Ord, V> Map<K, V> for RbTree<K, V> {
  #[inline]
  fn find<'a>(&'a self, key: &K) -> Option<&'a V> {
    self.root.as_ref().and_then(|node| node.find(key))
  }
}

pub struct RbTreeIterator<'a, K, V> {
  stack: ~[&'a Node<K, V>],
}

impl<'tree, K: Ord, V> RbTreeIterator<'tree, K, V> {
  fn push_left_tree(&mut self, root: Option<&'tree ~Node<K, V>>) {
    root.while_some(|node_ref| {
      self.stack.push(&**node_ref);
      node_ref.left.as_ref()
    });
  }

  fn pop_left_tree(&mut self, n: &'tree Node<K, V>) {
    let mut lchild = n;
    self.stack.pop_opt().while_some(|last| {
      if last.right.is_some() && ptr_eq(lchild, &**last.right.as_ref().unwrap()) {
        lchild = last;
        self.stack.pop_opt()
      } else {
        self.stack.push(last);
        None
      }
    });
  }
}

impl<'tree, K: Ord, V> Iterator<(&'tree K, &'tree V)> for RbTreeIterator<'tree, K, V> {
  fn next(&mut self) -> Option<(&'tree K, &'tree V)> {
    self.stack.pop_opt().map(|node| {
      if node.right.is_some() {
        self.stack.push(node);
        self.push_left_tree(node.right.as_ref());
      } else {
        self.pop_left_tree(node);
      }
      (&node.key, &node.data)
    })
  }
}

#[test]
fn test_insert() {
  let mut rbt = RbTree::new();
  rbt.insert("key5", "E");
  rbt.insert("key1", "A");
  rbt.insert("key3", "C");
  rbt.insert("key2", "B");
  rbt.insert("key4", "D");
  rbt.insert("key6", "F");
  rbt.insert("key7", "G");
  let ordered = ["A", "B", "C", "D", "E", "F", "G"];
  for ((_, v), expected) in rbt.iter().zip(ordered.iter()) {
    assert_eq!(v, expected);
  }
  let ref mut expected = RbTree::new();
  expected.root = Some(~Node::new("key5", "E"));
  expected.root.as_mut().unwrap().left = Some(~Node::new("key3", "C"));
  expected.root.as_mut().unwrap().right = Some(~Node::new("key7", "G"));
  expected.root.as_mut().unwrap().right.as_mut().unwrap().left = Some(~Node::new("key6", "F"));
  {
  let r = expected.root.as_mut().unwrap().left.as_mut().unwrap();
  r.right = Some(~Node::new("key4", "D"));
  r.left = Some(~Node::new("key2", "B"));
  r.left.as_mut().unwrap().left = Some(~Node::new("key1", "A"));
  }
  expected.len = 7;
  assert!(rbt.exact_eq(expected));
}

#[test]
fn test_swap() {
  let mut rbt = RbTree::new();
  rbt.insert("key3", "C");
  rbt.insert("key1", "A");
  rbt.insert("key2", "B").is_none() || fail!();
  rbt.insert("key1", "AA").unwrap() == "A" || fail!();
  let ordered = ["AA", "B", "C"];
  for ((_, v), expected) in rbt.iter().zip(ordered.iter()) {
    assert_eq!(v, expected);
  }
}

#[test]
fn test_equality() {
  let (t1, t2): (RbTree<~str, ~str>, RbTree<~str, ~str>) = (RbTree::new(), RbTree::new());
  assert_eq!(t1, t1);
  assert_eq!(t1, t2);
  assert_eq!(t2, t2);
  let mut t3 = RbTree::new();
  t3.insert(~"C", ~"valueC");
  t3.insert(~"A", ~"valueA");
  t3.insert(~"D", ~"valueD");
  t3.insert(~"B", ~"valueB");
  assert!(t1 != t3);
  let mut t4 = RbTree::new();
  t4.insert(~"B", ~"valueB");
  t4.insert(~"A", ~"valueA");
  t4.insert(~"C", ~"valueC");
  t4.insert(~"D", ~"valueD");
  assert_eq!(t3, t4);
}

#[test]
fn test_exact_equality() {
  let (t1, t2): (RbTree<~str, ~str>, RbTree<~str, ~str>) = (RbTree::new(), RbTree::new());
  assert!(t1.exact_eq(&t1));
  assert!(t1.exact_eq(&t2));
  assert!(t2.exact_eq(&t2));
  let mut t3 = RbTree::new();
  t3.insert(~"C", ~"valueC");
  t3.insert(~"A", ~"valueA");
  t3.insert(~"D", ~"valueD");
  t3.insert(~"B", ~"valueB");
  assert!(t1 != t3);
  let mut t4 = RbTree::new();
  t4.insert(~"B", ~"valueB");
  t4.insert(~"A", ~"valueA");
  t4.insert(~"C", ~"valueC");
  t4.insert(~"D", ~"valueD");
  assert!(!t3.exact_eq(&t4));
  let mut t5 = RbTree::new();
  t5.insert(~"A", ~"valueA");
  t5.insert(~"B", ~"valueB");
  t5.insert(~"C", ~"valueC");
  t5.insert(~"D", ~"valueD");
  assert!(!t3.exact_eq(&t5));
  assert!(t4.exact_eq(&t5));
}

#[test]
fn test_root_lrotate() {
  let ref mut tree = RbTree::new();
  tree.root = Some(~Node::new("X", "X"));
  tree.root.as_mut().unwrap().left = Some(~Node::new("A", "A"));
  tree.root.as_mut().unwrap().right = Some(~Node::new("Y", "Y"));
  tree.root.as_mut().unwrap().right.as_mut().unwrap().left = Some(~Node::new("B", "B"));
  tree.root.as_mut().unwrap().right.as_mut().unwrap().right = Some(~Node::new("C", "C"));
  let ref mut expected = RbTree::new();
  expected.root = Some(~Node::new("Y", "Y"));
  expected.root.as_mut().unwrap().left = Some(~Node::new("X", "X"));
  expected.root.as_mut().unwrap().left.as_mut().unwrap().left = Some(~Node::new("A", "A"));
  expected.root.as_mut().unwrap().left.as_mut().unwrap().right = Some(~Node::new("B", "B"));
  expected.root.as_mut().unwrap().right = Some(~Node::new("C", "C"));
  tree.root.as_mut().unwrap().lrotate();
  assert!(tree.exact_eq(expected));
}

#[test]
fn test_root_rrotate() {
  let ref mut tree = RbTree::new();
  tree.root = Some(~Node::new("Y", "Y"));
  tree.root.as_mut().unwrap().left = Some(~Node::new("X", "X"));
  tree.root.as_mut().unwrap().left.as_mut().unwrap().left = Some(~Node::new("A", "A"));
  tree.root.as_mut().unwrap().left.as_mut().unwrap().right = Some(~Node::new("B", "B"));
  tree.root.as_mut().unwrap().right = Some(~Node::new("C", "C"));
  let ref mut expected = RbTree::new();
  expected.root = Some(~Node::new("X", "X"));
  expected.root.as_mut().unwrap().left = Some(~Node::new("A", "A"));
  expected.root.as_mut().unwrap().right = Some(~Node::new("Y", "Y"));
  expected.root.as_mut().unwrap().right.as_mut().unwrap().left = Some(~Node::new("B", "B"));
  expected.root.as_mut().unwrap().right.as_mut().unwrap().right = Some(~Node::new("C", "C"));
  tree.root.as_mut().unwrap().rrotate();
  assert!(tree.exact_eq(expected));
}

#[test]
fn test_find() {
  let mut rbt = RbTree::new();
  rbt.insert(~"key3", ~"C");
  rbt.insert(~"key1", ~"A");
  rbt.insert(~"key2", ~"B");
  rbt.find(&~"key1").unwrap() == &~"A" || fail!();
  rbt.find(&~"key4").is_none() || fail!();
}

#[bench]
fn bench_insertion(b: &mut extra::test::BenchHarness) {
  use std::rand;
  use std::rand::Rng;
  let mut rng = rand::rng();
  let mut rbt = RbTree::new();
  b.iter(|| {
    rbt.insert(rng.gen::<int>(), 1);
  });
}

#[bench]
fn bench_insertion_2(b: &mut extra::test::BenchHarness) {
  let mut rbt = RbTree::new();
  rbt.insert("7",7);
  b.iter(|| {
    rbt.insert("1",1);
  });
}

#[bench]
fn bench_insertion_3(b: &mut extra::test::BenchHarness) {
  let mut rbt = RbTree::new();
  rbt.insert("7",7);
  rbt.insert("1",1);
  b.iter(|| {
    rbt.insert("3",1);
  });
}

#[bench]
fn bench_insertion_4(b: &mut extra::test::BenchHarness) {
  let mut rbt = RbTree::new();
  rbt.insert("7",7);
  rbt.insert("1",1);
  rbt.insert("3",1);
  b.iter(|| {
    rbt.insert("2",1);
  });
}

#[bench]
fn bench_insertion_5(b: &mut extra::test::BenchHarness) {
  let mut rbt = RbTree::new();
  rbt.insert("7",7);
  rbt.insert("1",1);
  rbt.insert("3",1);
  rbt.insert("2",1);
  b.iter(|| {
    rbt.insert("9",1);
  });
}

#[bench]
fn bench_insertion_6(b: &mut extra::test::BenchHarness) {
  let mut rbt = RbTree::new();
  rbt.insert("7",7);
  rbt.insert("1",1);
  rbt.insert("3",1);
  rbt.insert("2",1);
  rbt.insert("10",1);
  b.iter(|| {
    rbt.insert("8",1);
  });
}

#[bench]
fn bench_insertion_7(b: &mut extra::test::BenchHarness) {
  let mut rbt = RbTree::new();
  rbt.insert("7",7);
  rbt.insert("1",1);
  rbt.insert("3",1);
  rbt.insert("2",1);
  rbt.insert("10",1);
  rbt.insert("8",1);
  b.iter(|| {
    rbt.insert("9",1);
  });
}

#[bench]
fn bench_find(b: &mut extra::test::BenchHarness) {
  use std::rand;
  use std::rand::Rng;
  let mut rng = rand::rng();
  let mut rbt = RbTree::new();
  for i in range(0, 100) {
    rbt.insert(rng.gen_range(-100i, 100), i);
  }

  b.iter(|| {
    rbt.find(&rng.gen_range(-100i, 100));
  });
}

