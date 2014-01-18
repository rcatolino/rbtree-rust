#[feature(macro_rules)];
#[crate_id = "rbtree"];
#[feature(asm)];

extern mod extra;

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

/*
macro_rules! time (
  ($fnname: ident) => (let mut __sw__ = unsafe{Stopwatch::new(&mut __stats.$fnname)})
)
*/
macro_rules! time (
  ($fnname: ident) => (())
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

mkstats!(cf, color, paint, switch, pop, pop1, pop2, pop3, pop4, pop6, pop7, lrotate, rrotate, lrotate_flip, rrotate_flip, moveRedRight, moveRedLeft, fix)
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

type Color = u8;
static RED: u8 = 0;
static BLACK: u8 = 1;

struct Node<K, V> {
  color: Color,
  data: V,
  key: K,
  left: Option<~Node<K, V>>,
  right: Option<~Node<K, V>>,
}

trait Colored<K, V> {
  fn color(&self) -> Color;
  fn paint(&mut self, Color);
  fn switch_color(&mut self);
  fn insert(&mut self, key: K, value: V) -> Option<V>;
  fn pop(&mut self, key: &K) -> Option<V>;
  fn pop2(&mut self, key: &K) -> Option<V>;
  fn pop_min(&mut self) -> ~Node<K, V>;
}

impl<K: Ord, V> Colored<K, V> for Option<~Node<K, V>> {
  #[inline(always)]
  fn color(&self) -> Color {
    time!(color);
    match self {
      &None => BLACK,
      &Some(ref n) => n.color,
    }
  }

  #[inline(always)]
  fn paint(&mut self, c: Color) {
    time!(paint);
    self.as_mut().unwrap().color = c;
  }

  #[inline(always)]
  fn switch_color(&mut self) {
    time!(switch);
    self.as_mut().unwrap().color ^= 1;
  }

  fn insert(&mut self, key: K, val: V) -> Option<V> {
    match self {
      &None => {
        *self = Some(~Node::new(key, val));
        None
      }
      &Some(ref mut node) => {
        let ret = node.insert(key, val);
        node.fix();
        ret
      }
    }
  }

  fn pop_min(&mut self) -> ~Node<K, V> {
    let mut node = self.take_unwrap();
    match match node.left {
      None => return node,
      Some(ref lnode) => (lnode.color, lnode.left.color()),
    } {
      (BLACK, BLACK) => node.moveRedLeft(), _ => ()
    }
    let ret = node.left.pop_min();
    node.fix();
    *self = Some(node);
    ret
  }

  fn pop(&mut self, key: &K) -> Option<V> {
    match self.take() {
      None => return None,
      Some(mut node) => {
        let (lc, llc) = match node.left {
          Some(ref ln) => (ln.color, ln.left.color()),
          None => (BLACK, RED),
        };
        if *key < node.key {
          if lc == BLACK && llc == BLACK {
            time!(pop1);
            node.moveRedLeft();
          }
          let ret = node.left.pop(key);
          time!(pop2);
          node.fix();
          *self = Some(node);
          return ret;
        }
        if lc == RED {
          time!(pop3);
          node.rrotate();
        } else if !(*key > node.key) && node.right.is_none() {
          return Some(node.data);
        }
        if match node.right {
          Some(ref rn) => (rn.color, rn.left.color()),
          None => (BLACK, RED),
        } == (BLACK, BLACK) {
          time!(pop4);
          node.moveRedRight();
        }
        if *key > node.key {
          let ret = node.right.pop(key);
          time!(pop6);
          node.fix();
          *self = Some(node);
          return ret;
        }
        time!(pop7);
        let mut min = node.right.pop_min();
        let ~Node {left: l, right: r, color: c, data: d, key: _} = node;
        min.left = l;
        min.right = r;
        min.color = c;
        min.fix();
        *self = Some(min);
        return Some(d);
      }
    }
  }

  fn pop2(&mut self, key: &K) -> Option<V> {
    match self {
      &None => return None,
      &Some(_) => {
        if *key < self.as_ref().unwrap().key {
          let node = self.as_mut().unwrap();
          if node.left.color() == BLACK &&
             node.left.as_ref().map_or(BLACK, |n| n.left.color()) == BLACK {
            node.moveRedLeft();
          }
          let ret = node.left.pop(key);
          node.fix();
          return ret;
        }
        if self.as_ref().unwrap().left.color() == RED {
          self.as_mut().unwrap().rrotate();
        }
        if !(*key > self.as_ref().unwrap().key) &&
           self.as_ref().unwrap().right.is_none() {
          return self.take().map(|n| n.data);
        }
        {
          let node  = self.as_mut().unwrap();
          if node.right.is_some() && node.right.color() == BLACK &&
             node.right.as_ref().map_or(BLACK, |n| n.left.color()) == BLACK {
            node.moveRedRight();
          }
          if *key > node.key {
            let ret = node.right.pop(key);
            node.fix();
            return ret;
          }
        }
        let mut min = self.as_mut().unwrap().right.pop_min();
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

trait NodeRef<K, V> {
  fn moveRedLeft(&mut self);
  fn moveRedRight(&mut self);
  fn lrotate(&mut self);
  fn rrotate(&mut self);
  fn lrotate_flip(&mut self);
  fn rrotate_flip(&mut self);
  fn fix(&mut self);
}

impl<K: Ord, V> NodeRef<K, V> for ~Node<K, V> {
  fn moveRedLeft(&mut self) {
    time!(moveRedLeft);
    self.color_flip();
    if match self.right {
      Some(ref n) => n.left.color() == RED,
      None => fail!(),
    } {
      self.right.as_mut().unwrap().rrotate();
      self.lrotate_flip();
    }
  }

  fn moveRedRight(&mut self) {
    time!(moveRedRight);
    self.color_flip();
    if match self.left {
      Some(ref n) => n.left.color() == RED,
      None => fail!()
    } {
      self.rrotate_flip();
    }
  }

  #[inline(always)]
  fn lrotate(&mut self) {
    time!(lrotate);
    // Rotation of the root
    let mut y = self.right.take_unwrap();
    std::util::swap(self, &mut y);
    std::util::swap(&mut y.right, &mut self.left);
    self.color = y.color;
    y.color = RED;
    self.left = Some(y);
  }

  #[inline(always)]
  fn lrotate_flip(&mut self) {
    time!(lrotate_flip);
    // Rotation of the root
    let mut y = self.right.take_unwrap();
    std::util::swap(self, &mut y);
    std::util::swap(&mut y.right, &mut self.left);
    self.color = 1^y.color;
    y.color = BLACK;
    self.left = Some(y);
    self.right.switch_color();
  }

  #[inline(always)]
  fn rrotate(&mut self) {
    time!(rrotate);
    let mut y = self.left.take_unwrap();
    std::util::swap(self, &mut y);
    std::util::swap(&mut y.left, &mut self.right);
    self.color = y.color;
    y.color = RED;
    self.right = Some(y);
  }

  #[inline(always)]
  fn rrotate_flip(&mut self) {
    time!(rrotate_flip);
    let mut y = self.left.take_unwrap();
    std::util::swap(self, &mut y);
    std::util::swap(&mut y.left, &mut self.right);
    self.color = 1^y.color;
    y.color = BLACK;
    self.right = Some(y);
    self.left.switch_color();
  }

  fn fix(&mut self) {
    time!(fix);
    let lc = self.left.color();
    let rc = self.right.color();
    if lc == BLACK && rc == RED {
      self.lrotate();
      if self.right.color() == RED {
        self.color_flip();
      }
    } else if lc == RED && self.left.as_ref().unwrap().left.color() == RED {
      self.rrotate_flip();
    } else if lc == RED && rc == RED {
      self.color_flip();
    }
  }
}

impl<K: Ord, V> Node<K, V> {
  #[inline]
  fn new(key: K, val: V) -> Node<K, V> {
    Node {
      color: RED, data: val, key: key, left: None, right: None,
    }
  }

  #[inline]
  fn color_flip(&mut self) {
    time!(cf);
    self.color ^= 1;
    self.left.switch_color();
    self.right.switch_color();
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
    print!("{:?}({:?}) -> ", self.color, self.key);
    self.left.as_ref().map(|n| print!("{:?}({:?}) , ", n.color, n.key));
    self.right.as_ref().map(|n| print!(" , {:?}({:?})", n.color, n.key));
    print!("\n");
    self.left.as_ref().map(|n| n.print());
    self.right.as_ref().map(|n| n.print());
    print!("\n");
  }

  fn is_sound(&self) -> Result<~[uint], ~str> {
    let mut result = self.left.as_ref().map_or(Ok(~[]), |left| {
      if self.key <= left.key {
        Err(format!("Left child superior to node: {:?},{:?} -> {:?},{:?}",
                    self.key, self.data, left.key, left.data))
      } else if self.color == RED && left.color == RED {
        Err(format!("2 Red nodes in a raw : {:?} -> {:?}", self.key, left.key))
      } else {
        left.is_sound()
      }
    }).and_then(|mut lbh| {
      match self.right.as_ref().map_or(Ok(~[]), |right| {
        if self.key >= right.key {
          Err(format!("Right child inferior to node: {:?},{:?} -> {:?},{:?}",
                       self.key, self.data, right.key, right.data))
        } else if right.color == RED {
          Err(format!("Right leaning red node : {:?} -> {:?}", self.data, right.data))
        } else {
          right.is_sound()
        }
      }) {
        Ok(rbh) => {lbh.push_all_move(rbh); Ok(lbh)}, Err(msg) => Err(msg),
      }
    });
    result.as_mut().map(|bh| {
      if bh.is_empty() {
        // This is a leaf node.
        bh.push(0);
      }
      if self.color == BLACK {
        for height in bh.mut_iter() {
          *height += 1;
        }
      }
      bh
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

  pub fn iter<'a>(&'a self) -> RbTreeIterator<'a, K, V> {
    let mut iter = RbTreeIterator { stack: std::vec::with_capacity(m_depth(self.len)) };
    iter.push_left_tree(self.root.as_ref());
    iter
  }

  fn is_sound(&self) -> bool {
    let sound = self.root.as_ref().map_or(Ok(~[]), |n| n.is_sound());
    match sound {
      Ok(black_heights) => {
        for i in black_heights.iter() {
          if *i != black_heights[0] {
            println!("Unequals black heights. {:?}", black_heights);
            self.root.as_ref().unwrap().print();
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

impl<K: Ord, V> MutableMap<K, V> for RbTree<K, V> {
  fn swap(&mut self, k: K, v: V) -> Option<V> {
    let ret = self.root.insert(k, v);
    if ret.is_none() {
      self.len += 1;
    }
    self.root.as_mut().unwrap().color = BLACK;
    ret
  }


  fn pop(&mut self, k: &K) -> Option<V> {
    time!(pop);
    let ret = self.root.pop(k);
    if ret.is_some() {
      self.len -= 1;
    }
    self.root.paint(BLACK);
    ret
  }

  fn find_mut<'a>(&'a mut self, k: &K) -> Option<&'a mut V> {
    unsafe {
      self.find(k).map(|result| std::cast::transmute_mut(result))
    }
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
    let mut next = &self.root;
    loop {
      match next {
        &Some(ref node) => {
          if *key < node.key {
            next = &node.left;
          } else if *key > node.key {
            next = &node.right;
          } else {
            return Some(&node.data);
          }
        }
        &None => return None,
      }
    }
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
  rbt.find_mut(&~"key2").map(|ret| ret.push_str("D"));
  rbt.find(&~"key2").unwrap() == &~"BD" || fail!();
  rbt.is_sound() || fail!();
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
  for i in range(0, 10) {
    rbt.insert(rng.gen_range(-100i, 100), i);
    rbt.is_sound() || fail!();
  }
  for _ in range(0, 50) {
    rbt.pop(&rng.gen_range(-100i,100));
    rbt.is_sound() || fail!();
  }
}

#[test]
fn test_pop_measured() {
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
  rbt.pop(&~"key3").unwrap() == ~"C" || fail!();
  print_stats!(lrotate);
  print_stats!(rrotate);
  print_stats!(lrotate_flip);
  print_stats!(rrotate_flip);
  print_stats!(fix);
  print_stats!(moveRedLeft);
  print_stats!(moveRedRight);
  print_stats!(color);
  print_stats!(cf);
  print_stats!(paint);
  print_stats!(switch);
  print_stats!(pop);
  print_stats!(pop1);
  print_stats!(pop2);
  print_stats!(pop3);
  print_stats!(pop4);
  print_stats!(pop6);
  print_stats!(pop7);
}

#[bench]
fn bench_insertion_empty(b: &mut extra::test::BenchHarness) {
  b.iter(|| {
    let mut rbt = RbTree::new();
    rbt.insert(1, 1);
  });
}

#[bench]
fn bench_insertion(b: &mut extra::test::BenchHarness) {
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
fn bench_insert_pop(b: &mut extra::test::BenchHarness) {
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

#[bench]
fn bench_insertion_empty_tm(b: &mut extra::test::BenchHarness) {
  use extra::treemap::TreeMap;
  b.iter(|| {
    let mut rbt = TreeMap::new();
    rbt.insert(1, 1);
  });
}

#[bench]
fn bench_insertion_tm(b: &mut extra::test::BenchHarness) {
  use std::rand;
  use std::rand::Rng;
  use extra::treemap::TreeMap;
  let mut rng = rand::rng();
  b.iter(|| {
    let mut rbt = TreeMap::new();
    for i in range(0, 50) {
      rbt.insert(rng.gen_range(-100i, 100), i);
    }
  });
}

#[bench]
fn bench_insert_pop_tm(b: &mut extra::test::BenchHarness) {
  use std::rand;
  use std::rand::Rng;
  use extra::treemap::TreeMap;
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
fn bench_find_tm(b: &mut extra::test::BenchHarness) {
  use std::rand;
  use std::rand::Rng;
  use extra::treemap::TreeMap;
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
fn bench_insertion_empty_hm(b: &mut extra::test::BenchHarness) {
  use std::hashmap::HashMap;
  b.iter(|| {
    let mut rbt = HashMap::new();
    rbt.insert(1, 1);
  });
}

#[bench]
fn bench_insertion_hm(b: &mut extra::test::BenchHarness) {
  use std::rand;
  use std::rand::Rng;
  use std::hashmap::HashMap;
  let mut rng = rand::rng();
  b.iter(|| {
    let mut rbt = HashMap::new();
    for i in range(0, 50) {
      rbt.insert(rng.gen_range(-100i, 100), i);
    }
  });
}

#[bench]
fn bench_insert_pop_hm(b: &mut extra::test::BenchHarness) {
  use std::rand;
  use std::rand::Rng;
  use std::hashmap::HashMap;
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
fn bench_find_hm(b: &mut extra::test::BenchHarness) {
  use std::rand;
  use std::rand::Rng;
  use std::hashmap::HashMap;
  let mut rng = rand::rng();
  let mut rbt = HashMap::new();
  for i in range(0, 100) {
    rbt.insert(rng.gen_range(-100i, 100), i);
  }

  b.iter(|| {
    rbt.find(&rng.gen_range(-100i, 100));
  });
}
