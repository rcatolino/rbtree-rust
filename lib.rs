#[allow(unused_imports)]; // This is for the timer code, only used when the macros are invoked.
#[feature(macro_rules)];
#[crate_id = "rbtree"];
#[crate_type = "lib"];
#[feature(asm)];

extern crate time;
extern crate collections;
extern crate test;

use test::BenchHarness;

use timer::{Stats, Stopwatch};
mod timer;

macro_rules! mkstats (
  ($fn1: ident $(,$fnname: ident)* ) => (

    struct __stats__struct {
      dyn_tim: Option<Stopwatch>,
      $fn1: Stats,
      $(
        $fnname: Stats,
       )*
    }
    static mut __stats: __stats__struct = __stats__struct {
      dyn_tim: None,
      $fn1: Stats {times_called: 0, min: -1 as u64, max: 0, cumul: 0},
      $(
        $fnname: Stats {times_called: 0, min: -1 as u64, max: 0, cumul: 0},
       )*
    };
  )
)

macro_rules! print_stats (
  ($fn1: ident) => (
    unsafe{
      println!("  timer {} :", stringify!($fn1));
      println!("    -Called {} times", __stats.$fn1.times_called);
      println!("    -Min {} ns", __stats.$fn1.min);
      println!("    -Max {} ns", __stats.$fn1.max);
      println!("    -Avg {} ns", __stats.$fn1.avg());
      println!("    -Total {} ns", __stats.$fn1.cumul);
    }
  )
)

/*
macro_rules! time (
  ($fnname: ident) => (let mut __sw__ = unsafe{Stopwatch::new(&mut __stats.$fnname)})
)

mkstats!(cf, switch, pop, pop1, pop2, pop3, pop4, pop6, pop7, lrotate, rrotate,
         lrotate_flip, rrotate_flip, moveRedRight, moveRedLeft, fix)
*/
macro_rules! time (
  ($fnname: ident) => (())
)


#[inline]
#[cfg(target_arch = "x86_64")] #[cfg(target_arch = "x86")]
// yeah, yeah i know...
fn m_depth(n: uint) -> uint {
  unsafe {
    let mut ret: uint;
    asm!("bsr $1, $0" : "=r"(ret) : "r"(n) :: "volatile");
    return 2*ret+1;
  }
}

#[inline]
fn ptr_eq<T>(t1: &T, t2: &T) -> bool {
  t1 as *T == t2 as *T
}

type Color = u8;
static RED: u8 = 0;
static BLACK: u8 = 1;

#[deriving(Show)]
struct Node<K, V> {
  data: V,
  key: K,
  left: ColoredNode<K, V>,
  right: ColoredNode<K, V>,
}

#[deriving(Show)]
struct ColoredNode<K, V> {
  color: Color,
  node: Option<~Node<K, V>>
}

impl<K: Ord, V: Eq> Eq for ColoredNode<K, V> {
  fn eq(&self, other: &ColoredNode<K, V>) -> bool {
    self.node == other.node
  }
}

impl<K: Ord, V> ColoredNode<K, V> {
  #[inline(always)]
  fn switch_color(&mut self) {
    time!(switch);
    self.color ^= 1;
  }

  fn insert(&mut self, key: K, mut val: V) -> Option<V> {
    match self.node {
      None => {
        self.node = Some(~Node::new(key, val));
        self.color = RED;
        None
      }
      Some(ref mut n) => {
        if key < n.key {
          let ret = n.left.insert(key, val);
          let (lc, rc) = (n.left.color, n.right.color);
          if lc == RED && n.left.node.as_ref().unwrap().left.color == RED {
            n.rrotate_flip(&mut self.color);
          } else if lc == RED && rc == RED {
            n.color_flip(&mut self.color);
          }
          ret
        } else if key > n.key {
          let ret = n.right.insert(key, val);
          let (lc, rc) = (n.left.color, n.right.color);
          if lc == BLACK && rc == RED {
            n.lrotate();
            if n.right.color == RED {
              n.color_flip(&mut self.color);
            }
          } else if lc == RED && rc == RED {
            n.color_flip(&mut self.color);
          }
          ret
        } else {
          std::mem::swap(&mut n.data, &mut val);
          Some(val)
        }
      }
    }
  }

  fn pop_min(&mut self) -> ~Node<K, V> {
    let mut node = self.node.take_unwrap();
    if node.left.node.is_none() {
      self.color = BLACK;
      return node;
    } else if node.left.color == BLACK && node.left.node.as_ref().unwrap().left.color == BLACK {
      node.moveRedLeft(&mut self.color);
    }
    let ret = node.left.pop_min();
    node.fix(&mut self.color);
    self.node = Some(node);
    ret
  }

  fn pop(&mut self, key: &K) -> Option<V> {
    time!(pop);
    match self.node.take() {
      None => return None,
      Some(mut node) => {
        if *key < node.key {
          if node.left.color == BLACK && match node.left.node {
            Some(ref ln) => ln.left.color == BLACK,
            None => false,
          } {
            time!(pop1);
            node.moveRedLeft(&mut self.color);
          }
          let ret = node.left.pop(key);
          time!(pop2);
          node.fix(&mut self.color);
          self.node = Some(node);
          return ret;
        }
        if node.left.color == RED {
          time!(pop3);
          node.rrotate();
        } else if !(*key > node.key) && node.right.node.is_none() {
          self.color = BLACK;
          return Some(node.data);
        } else if node.right.color == BLACK && match node.right.node {
          Some(ref rn) => rn.left.color == BLACK,
          None => false,
        } {
          time!(pop4);
          node.moveRedRight(&mut self.color);
        }
        if *key > node.key {
          let ret = node.right.pop(key);
          time!(pop6);
          node.fix(&mut self.color);
          self.node = Some(node);
          return ret;
        }
        time!(pop7);
        let mut min = node.right.pop_min();
        let ~Node {left: l, right: r, data: d, key: _} = node;
        min.left = l;
        min.right = r;
        min.fix(&mut self.color);
        self.node = Some(min);
        return Some(d);
      }
    }
  }

}

#[doc(hidden)]
priv trait NodeRef<K, V> {
  fn moveRedLeft(&mut self, c: &mut Color);
  fn moveRedRight(&mut self, c: &mut Color);
  fn lrotate(&mut self);
  fn rrotate(&mut self);
  fn lrotate_flip(&mut self, c: &mut Color);
  fn rrotate_flip(&mut self, c: &mut Color);
  fn fix(&mut self, c: &mut Color);
}

impl<K: Ord, V> NodeRef<K, V> for ~Node<K, V> {
  fn moveRedLeft(&mut self, c: &mut Color) {
    time!(moveRedLeft);
    self.color_flip(c);
    if match self.right.node {
      Some(ref n) => n.left.color == RED,
      None => fail!(),
    } {
      self.right.node.as_mut().unwrap().rrotate();
      self.lrotate_flip(c);
    }
  }

  fn moveRedRight(&mut self, c: &mut Color) {
    time!(moveRedRight);
    self.color_flip(c);
    if match self.left.node {
      Some(ref n) => n.left.color == RED,
      None => fail!()
    } {
      self.rrotate_flip(c);
    }
  }

  #[inline(always)]
  fn lrotate(&mut self) {
    time!(lrotate);
    // Rotation of the root
    let mut y = self.right.node.take_unwrap();
    std::mem::swap(self, &mut y);
    std::mem::swap(&mut y.right.node, &mut self.left.node);
    y.right.color = self.left.color;
    self.left.color = RED;
    self.left.node = Some(y);
  }

  #[inline(always)]
  fn lrotate_flip(&mut self, c: &mut Color) {
    time!(lrotate_flip);
    // Rotation of the root
    let mut y = self.right.node.take_unwrap();
    std::mem::swap(self, &mut y);
    std::mem::swap(&mut y.right.node, &mut self.left.node);
    y.right.color = self.left.color;
    *c ^= 1;
    self.left.color = BLACK;
    self.left.node = Some(y);
    self.right.switch_color();
  }

  #[inline(always)]
  fn rrotate(&mut self) {
    time!(rrotate);
    let mut y = self.left.node.take_unwrap();
    std::mem::swap(self, &mut y);
    std::mem::swap(&mut y.left.node, &mut self.right.node);
    y.left.color = self.right.color;
    self.right.color = RED;
    self.right.node = Some(y);
  }

  #[inline(always)]
  fn rrotate_flip(&mut self, c: &mut Color) {
    time!(rrotate_flip);
    let mut y = self.left.node.take_unwrap();
    std::mem::swap(self, &mut y);
    std::mem::swap(&mut y.left.node, &mut self.right.node);
    y.left.color = self.right.color;
    *c ^= 1;
    self.right.color = BLACK;
    self.right.node = Some(y);
    self.left.switch_color();
  }

  fn fix(&mut self, c: &mut Color) {
    time!(fix);
    let (lc, rc) = (self.left.color, self.right.color);
    if lc == BLACK && rc == RED {
      self.lrotate();
      if self.right.color == RED {
        self.color_flip(c);
      }
    } else if lc == RED && self.left.node.as_ref().unwrap().left.color == RED {
      self.rrotate_flip(c);
    } else if lc == RED && rc == RED {
      self.color_flip(c);
    }
  }
}

impl<K: Ord, V> Node<K, V> {
  #[inline]
  fn new(key: K, val: V) -> Node<K, V> {
    Node {
      data: val, key: key, left: ColoredNode { color: BLACK, node: None},
      right: ColoredNode { color: BLACK, node: None },
    }
  }

  #[inline]
  fn color_flip(&mut self, c: &mut Color) {
    time!(cf);
    *c ^= 1;
    self.left.switch_color();
    self.right.switch_color();
  }

  fn print(&self, c: Color) {
    print!("{:?}({:?}) -> ", c, self.key);
    self.left.node.as_ref().map(|n| print!("{:?}({:?}) , ", self.left.color, n.key));
    self.right.node.as_ref().map(|n| print!(" , {:?}({:?})", self.right.color, n.key));
    print!("\n");
    self.left.node.as_ref().map(|n| n.print(self.left.color));
    self.right.node.as_ref().map(|n| n.print(self.right.color));
    print!("\n");
  }

  fn is_sound(&self, c: Color) -> Result<~[uint], ~str> {
    if self.left.color == RED && self.left.node.is_none() {
      return Err(format!("Red left leaf for {:?}", self.key));
    } else if self.right.color == RED && self.right.node.is_none() {
      return Err(format!("Red left leaf for {:?}", self.key));
    }
    let mut result = self.left.node.as_ref().map_or(Ok(~[]), |left| {
      if self.key <= left.key {
        Err(format!("Left child superior to node: {:?},{:?} -> {:?},{:?}",
                    self.key, self.data, left.key, left.data))
      } else if c == RED && self.left.color == RED {
        Err(format!("2 Red nodes in a raw : {:?} -> {:?}", self.key, left.key))
      } else {
        left.is_sound(self.left.color)
      }
    }).and_then(|mut lbh| {
      match self.right.node.as_ref().map_or(Ok(~[]), |right| {
        if self.key >= right.key {
          Err(format!("Right child inferior to node: {:?},{:?} -> {:?},{:?}",
                       self.key, self.data, right.key, right.data))
        } else if self.right.color == RED {
          Err(format!("Right leaning red node : {:?} -> {:?}", self.data, right.data))
        } else {
          right.is_sound(self.right.color)
        }
      }) {
        Ok(rbh) => {lbh.push_all_move(rbh); Ok(lbh)}, Err(msg) => Err(msg),
      }
    });
    let _ = result.as_mut().map(|bh| {
      if bh.is_empty() {
        // This is a leaf node.
        bh.push(0);
      }
      if c == BLACK {
        for height in bh.mut_iter() {
          *height += 1;
        }
      }
    });
    return result;
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

#[deriving(Show)]
pub struct RbTree<K, V> {
  priv root: ColoredNode<K, V>,
  priv len: uint,
}

impl<K: Ord, V> RbTree<K, V> {
  /// Creates a new tree.
  pub fn new() -> RbTree<K, V> {
    RbTree {
      root: ColoredNode { color: BLACK, node: None }, len: 0,
    }
  }

  /// Returns an iterator over the tree nodes.
  /// The nodes are iterated in their key's order.
  pub fn iter<'tree>(&'tree self) -> Entries<'tree, K, V> {
    let mut iter = Entries { stack: std::vec::with_capacity(m_depth(self.len)) };
    iter.push_left_tree(self.root.node.as_ref());
    iter
  }

  // Print and is_sound are only usefull for testing/debugging purposes.
  #[allow(dead_code)]
  fn print(&self) {
    self.root.node.as_ref().unwrap().print(self.root.color);
  }

  #[allow(dead_code)]
  fn is_sound(&self) -> bool {
    let sound = self.root.node.as_ref().map_or(Ok(~[]), |n| n.is_sound(self.root.color));
    match sound {
      Ok(black_heights) => {
        for i in black_heights.iter() {
          if *i != black_heights[0] {
            println!("Unequals black heights. {:?}", black_heights);
            self.root.node.as_ref().unwrap().print(self.root.color);
            return false;
          }
        }
        return true;
      }
      Err(msg) => {
        println!("{}", msg);
        return false;
      }
    }
  }
}

impl<K: Ord+Eq, V: Eq> RbTree<K, V> {
  /// Returns true if both trees contain the same values and
  /// have the same layout.
  pub fn exact_eq(&self, other: &RbTree<K, V>) -> bool {
    self.len == other.len && self.root.node == other.root.node
  }
}

impl<K, V> Container for RbTree<K, V> {
  /// Returns the number of elements stored in the tree.
  fn len(&self) -> uint {
    self.len
  }
}

impl<K: Ord, V> MutableMap<K, V> for RbTree<K, V> {
  /// Insert a key-value pair from the map. If the key already had a value
  /// present in the map, that value is returned. Otherwise None is returned.
  fn swap(&mut self, k: K, v: V) -> Option<V> {
    let ret = self.root.insert(k, v);
    if ret.is_none() {
      self.len += 1;
    }
    self.root.color = BLACK;
    ret
  }

  /// Removes a key from the map, returning the value at the key if the key
  /// was previously in the map.
  fn pop(&mut self, k: &K) -> Option<V> {
    let ret = self.root.pop(k);
    if ret.is_some() {
      self.len -= 1;
    }
    self.root.color = BLACK;
    ret
  }

  /// Return a mutable reference to the value corresponding to the key
  fn find_mut<'a>(&'a mut self, k: &K) -> Option<&'a mut V> {
    unsafe {
      self.find(k).map(|result| std::cast::transmute_mut(result))
    }
  }
}

impl<K, V> Mutable for RbTree<K, V> {
  /// Clear the container, removing all values.
  fn clear(&mut self) {
    self.root.node.take();
    self.len = 0;
  }
}

impl<K: Ord+Eq, V: Eq> Eq for RbTree<K, V> {
  /// Returns true if both trees contain the same values.
  fn eq(&self, other: &RbTree<K, V>) -> bool {
    self.len == other.len && self.iter().to_owned_vec() == other.iter().to_owned_vec()
  }
}

impl<K: Ord, V> Map<K, V> for RbTree<K, V> {
  /// Return a reference to the value corresponding to the key
  fn find<'a>(&'a self, key: &K) -> Option<&'a V> {
    let mut next = &self.root.node;
    loop {
      match next {
        &Some(ref node) => {
          if *key < node.key {
            next = &node.left.node;
          } else if *key > node.key {
            next = &node.right.node;
          } else {
            return Some(&node.data);
          }
        }
        &None => return None,
      }
    }
  }
}

pub struct Entries<'tree, K, V> {
  priv stack: ~[&'tree Node<K, V>],
}

impl<'tree, K: Ord, V> Entries<'tree, K, V> {
  fn push_left_tree(&mut self, root: Option<&'tree ~Node<K, V>>) {
    root.while_some(|node_ref| {
      self.stack.push(&**node_ref);
      node_ref.left.node.as_ref()
    });
  }

  fn pop_left_tree(&mut self, n: &'tree Node<K, V>) {
    let mut lchild = n;
    self.stack.pop().while_some(|last| {
      if last.right.node.is_some() && ptr_eq(lchild, &**last.right.node.as_ref().unwrap()) {
        lchild = last;
        self.stack.pop()
      } else {
        self.stack.push(last);
        None
      }
    });
  }
}

impl<'tree, K: Ord, V> Iterator<(&'tree K, &'tree V)> for Entries<'tree, K, V> {
  fn next(&mut self) -> Option<(&'tree K, &'tree V)> {
    self.stack.pop().map(|node| {
      if node.right.node.is_some() {
        self.stack.push(node);
        self.push_left_tree(node.right.node.as_ref());
      } else {
        self.pop_left_tree(node);
      }
      (&node.key, &node.data)
    })
  }
}

// Used in the tests.
#[allow(dead_code)]
fn mkcn<K: Ord, V>(k: K, v: V) -> ColoredNode<K, V> {
  ColoredNode { color: BLACK, node: Some(~Node::new(k, v)), }
}

#[test]
fn test_insert() {
  let mut rbt = RbTree::new();
  rbt.insert("key5", "E");
  rbt.is_sound() || fail!();
  rbt.insert("key1", "A");
  rbt.is_sound() || fail!();
  rbt.insert("key3", "C");
  rbt.is_sound() || fail!();
  rbt.insert("key2", "B");
  rbt.is_sound() || fail!();
  rbt.insert("key4", "D");
  rbt.is_sound() || fail!();
  rbt.insert("key6", "F");
  rbt.is_sound() || fail!();
  rbt.insert("key7", "G");
  rbt.is_sound() || fail!();
  let ordered = ["A", "B", "C", "D", "E", "F", "G"];
  for ((_, v), expected) in rbt.iter().zip(ordered.iter()) {
    assert_eq!(v, expected);
  }
  let ref mut expected = RbTree::new();
  expected.root = mkcn("key5", "E");
  {
    let root = expected.root.node.as_mut().unwrap();
    root.left = mkcn("key3", "C");
    root.right = mkcn("key7", "G");
    root.right.node.as_mut().unwrap().left = mkcn("key6", "F");
    {
      let r = root.left.node.as_mut().unwrap();
      r.right = mkcn("key4", "D");
      r.left = mkcn("key2", "B");
      r.left.node.as_mut().unwrap().left = mkcn("key1", "A");
    }
  }
  expected.len = 7;
  assert!(rbt.exact_eq(expected));
}

#[test]
fn test_swap() {
  let mut rbt = RbTree::new();
  rbt.insert("key3", "C");
  rbt.insert("key1", "A");
  rbt.swap("key2", "B").is_none() || fail!();
  rbt.is_sound() || fail!();
  rbt.swap("key1", "AA").unwrap() == "A" || fail!();
  rbt.is_sound() || fail!();
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
  tree.root = mkcn("X", "X");
  tree.root.node.as_mut().unwrap().left = mkcn("A", "A");
  tree.root.node.as_mut().unwrap().right = mkcn("Y", "Y");
  tree.root.node.as_mut().unwrap().right.node.as_mut().unwrap().left = mkcn("B", "B");
  tree.root.node.as_mut().unwrap().right.node.as_mut().unwrap().right = mkcn("C", "C");
  let ref mut expected = RbTree::new();
  expected.root = mkcn("Y", "Y");
  expected.root.node.as_mut().unwrap().left = mkcn("X", "X");
  expected.root.node.as_mut().unwrap().left.node.as_mut().unwrap().left = mkcn("A", "A");
  expected.root.node.as_mut().unwrap().left.node.as_mut().unwrap().right = mkcn("B", "B");
  expected.root.node.as_mut().unwrap().right = mkcn("C", "C");
  tree.root.node.as_mut().unwrap().lrotate();
  assert!(tree.exact_eq(expected));
}

#[test]
fn test_root_rrotate() {
  let ref mut tree = RbTree::new();
  tree.root = mkcn("Y", "Y");
  tree.root.node.as_mut().unwrap().left = mkcn("X", "X");
  tree.root.node.as_mut().unwrap().left.node.as_mut().unwrap().left = mkcn("A", "A");
  tree.root.node.as_mut().unwrap().left.node.as_mut().unwrap().right = mkcn("B", "B");
  tree.root.node.as_mut().unwrap().right = mkcn("C", "C");
  let ref mut expected = RbTree::new();
  expected.root = mkcn("X", "X");
  expected.root.node.as_mut().unwrap().left = mkcn("A", "A");
  expected.root.node.as_mut().unwrap().right = mkcn("Y", "Y");
  expected.root.node.as_mut().unwrap().right.node.as_mut().unwrap().left = mkcn("B", "B");
  expected.root.node.as_mut().unwrap().right.node.as_mut().unwrap().right = mkcn("C", "C");
  tree.root.node.as_mut().unwrap().rrotate();
  assert!(tree.exact_eq(expected));
}

#[test]
fn test_find() {
  let mut rbt = RbTree::new();
  rbt.insert(~"key3", ~"C");
  rbt.insert(~"key1", ~"A");
  rbt.insert(~"key2", ~"B");
  rbt.is_sound() || fail!();
  rbt.find(&~"key1").unwrap() == &~"A" || fail!();
  rbt.find(&~"key4").is_none() || fail!();
  rbt.find_mut(&~"key2").map(|ret| ret.push_str("D"));
  rbt.find(&~"key2").unwrap() == &~"BD" || fail!();
}

#[test]
fn test_pop1() {
  let mut rbt = RbTree::new();
  rbt.insert(~"key7", ~"G");
  rbt.insert(~"key1", ~"A");
  rbt.insert(~"key3", ~"C");
  rbt.insert(~"key8", ~"H");
  rbt.insert(~"key2", ~"B");
  rbt.insert(~"key4", ~"D");
  rbt.insert(~"key5", ~"E");
  rbt.insert(~"key9", ~"I");
  rbt.insert(~"key6", ~"F");
  rbt.is_sound() || fail!();
  rbt.pop(&~"key3").unwrap() == ~"C" || fail!();
  rbt.is_sound() || fail!();
  rbt.pop(&~"notakey").is_none() || fail!();
  rbt.is_sound() || fail!();
  rbt.pop(&~"key5").unwrap() == ~"E" || fail!();
  rbt.is_sound() || fail!();
  rbt.pop(&~"key1").unwrap() == ~"A" || fail!();
  rbt.is_sound() || fail!();
  rbt.pop(&~"key9").unwrap() == ~"I" || fail!();
  rbt.is_sound() || fail!();
  rbt.is_empty() && fail!();
}

#[test]
fn test_pop2() {
  use std::rand;
  use std::rand::Rng;
  let mut rng = rand::rng();
  let mut rbt = RbTree::new();
  let n = 60i;
  for i in range(0, n) {
    rbt.insert(rng.gen_range(-2*n, 2*n), i);
    rbt.is_sound() || fail!();
  }
  for _ in range(0, n) {
    rbt.pop(&rng.gen_range(-2*n, 2*n));
    rbt.is_sound() || fail!();
  }
}

  /*
#[test]
fn test_pop_measured() {
  use std::rand;
  use std::rand::Rng;
  let mut rng = rand::rng();
  let mut rbt = RbTree::new();
  let n = 60i;
  for i in range(0, n) {
    rbt.insert(rng.gen_range(-2*n, 2*n), i);
    rbt.is_sound() || fail!();
  }
  for _ in range(0, n) {
    rbt.pop(&rng.gen_range(-2*n, 2*n));
    rbt.is_sound() || fail!();
  }
  print_stats!(lrotate);
  print_stats!(rrotate);
  print_stats!(lrotate_flip);
  print_stats!(rrotate_flip);
  print_stats!(fix);
  print_stats!(moveRedLeft);
  print_stats!(moveRedRight);
  print_stats!(cf);
  print_stats!(switch);
  print_stats!(pop);
  print_stats!(pop1);
  print_stats!(pop2);
  print_stats!(pop3);
  print_stats!(pop4);
  print_stats!(pop6);
  print_stats!(pop7);
}
  */

#[bench]
fn bench_insertion_empty(b: &mut BenchHarness) {
  b.iter(|| {
    let mut rbt = RbTree::new();
    rbt.insert(1, 1);
  });
}

#[bench]
fn bench_insertion(b: &mut BenchHarness) {
  use std::rand;
  use std::rand::Rng;
  let mut rng = rand::rng();
  b.iter(|| {
    let mut rbt = RbTree::new();
    for i in range(0, 50) {
      rbt.insert(rng.gen_range(-100i, 100), i);
    }
  });
}

#[bench]
fn bench_insert_pop(b: &mut BenchHarness) {
  use std::rand;
  use std::rand::Rng;
  let mut rng = rand::rng();
  b.iter(|| {
    let mut rbt = RbTree::new();
    for i in range(0, 50) {
      rbt.insert(rng.gen_range(-100i, 100), i);
    }
    for _ in range(0, 50) {
      rbt.pop(&rng.gen_range(-100i,100));
    }
  });
}

#[bench]
fn bench_find(b: &mut BenchHarness) {
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

#[bench]
fn bench_insertion_empty_tm(b: &mut BenchHarness) {
  use collections::treemap::TreeMap;
  b.iter(|| {
    let mut rbt = TreeMap::new();
    rbt.insert(1, 1);
  });
}

#[bench]
fn bench_insertion_tm(b: &mut BenchHarness) {
  use std::rand;
  use std::rand::Rng;
  use collections::treemap::TreeMap;
  let mut rng = rand::rng();
  b.iter(|| {
    let mut rbt = TreeMap::new();
    for i in range(0, 50) {
      rbt.insert(rng.gen_range(-100i, 100), i);
    }
  });
}

#[bench]
fn bench_insert_pop_tm(b: &mut BenchHarness) {
  use std::rand;
  use std::rand::Rng;
  use collections::treemap::TreeMap;
  let mut rng = rand::rng();
  b.iter(|| {
    let mut rbt = TreeMap::new();
    for i in range(0, 50) {
      rbt.insert(rng.gen_range(-100i, 100), i);
    }
    for _ in range(0, 50) {
      rbt.pop(&rng.gen_range(-100i,100));
    }
  });
}

#[bench]
fn bench_find_tm(b: &mut BenchHarness) {
  use std::rand;
  use std::rand::Rng;
  use collections::treemap::TreeMap;
  let mut rng = rand::rng();
  let mut rbt = TreeMap::new();
  for i in range(0, 100) {
    rbt.insert(rng.gen_range(-100i, 100), i);
  }

  b.iter(|| {
    rbt.find(&rng.gen_range(-100i, 100));
  });
}

#[bench]
fn bench_insertion_empty_hm(b: &mut BenchHarness) {
  use collections::hashmap::HashMap;
  b.iter(|| {
    let mut rbt = HashMap::new();
    rbt.insert(1, 1);
  });
}

#[bench]
fn bench_insertion_hm(b: &mut BenchHarness) {
  use std::rand;
  use std::rand::Rng;
  use collections::hashmap::HashMap;
  let mut rng = rand::rng();
  b.iter(|| {
    let mut rbt = HashMap::new();
    for i in range(0, 50) {
      rbt.insert(rng.gen_range(-100i, 100), i);
    }
  });
}

#[bench]
fn bench_insert_pop_hm(b: &mut BenchHarness) {
  use std::rand;
  use std::rand::Rng;
  use collections::hashmap::HashMap;
  let mut rng = rand::rng();
  b.iter(|| {
    let mut rbt = HashMap::new();
    for i in range(0, 50) {
      rbt.insert(rng.gen_range(-100i, 100), i);
    }
    for _ in range(0, 50) {
      rbt.pop(&rng.gen_range(-100i,100));
    }
  });
}

#[bench]
fn bench_find_hm(b: &mut BenchHarness) {
  use std::rand;
  use std::rand::Rng;
  use collections::hashmap::HashMap;
  let mut rng = rand::rng();
  let mut rbt = HashMap::new();
  for i in range(0, 100) {
    rbt.insert(rng.gen_range(-100i, 100), i);
  }

  b.iter(|| {
    rbt.find(&rng.gen_range(-100i, 100));
  });
}
