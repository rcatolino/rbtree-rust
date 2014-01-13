#[crate_id = "rbtree"];
#[feature(asm)];

#[cfg(target_arch = "x86_64")] #[cfg(target_arch = "x86")]
#[inline(always)]
// yeah, yeah i know...
fn m_depth(n: uint) -> uint {
  unsafe {
    let mut ret: uint;
    asm!("bsr $1, $0" : "=r"(ret) : "r"(n) :: "volatile");
    return ret+1;
  }
}

#[inline(always)]
fn ptr_eq<T>(t1: &T, t2: &T) -> bool {
  std::ptr::to_unsafe_ptr(t1) == std::ptr::to_unsafe_ptr(t2)
}

#[deriving(Eq)]
enum Color {
  Red,
  Black,
}

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

impl<K: Ord, V> Node<K, V> {
  fn new(key: K, val: V) -> Node<K, V> {
    Node {
      color: Black, data: val, key: key, left: None, right: None,
    }
  }

  fn lrotate(&mut self, what: Child) -> bool {
    // Get the parent pointer to x.
    let local_root = match what {
      Left => &mut self.left, Right => &mut self.right,
    };

    // Check wether there is something to rotate.
    if local_root.as_ref().and_then(|x| x.right.as_ref()).is_none() {
      return false; // Either x or y is None.
    }

    // Unroot x and y.
    let mut x = local_root.take_unwrap();
    let mut y = x.right.take_unwrap();
    // Rotate
    x.right = y.left.take();
    y.left = Some(x);
    // Reroot
    *local_root = Some(y);
    true
  }

  fn insert(&mut self, key: K, val: V, stack: &mut StackAcc<K, V>) -> bool {
    let child_opt = if key < self.key {
      &mut self.left
    } else if key > self.key {
      &mut self.right
    } else {
      return false;
    };

    *child_opt = match child_opt.as_mut() {
      None => {
        let mut new = ~Node::new(key, val);
        stack.push_node(&mut *new);
        Some(new)
      }
      Some(child) => {
        stack.push_node(&mut **child);
        return child.insert(key, val, stack);
      }
    };
    true
  }

}

// What this is :
// Well, during the insertion step we need to keep references to all the nodes
// on the path between the root and the inserted values. We need those refs
// to perform all modification necessary to rebalance the tree.
// There are several ways to keep those refs.
// - Use the call stack: Perform the tree-rebalancing while unwinding
// from the recursive insert call. This way we use the call stack to keep
// our references and we never have more than one mutable reference to a node.
// - Use a separate stack: Preallocate a vector in the beginning, and add a
// reference to each node on the path in it. The problem is, while going to
// the insert calls we will end up with two mutable references to each node:
// the one that's used to call the insert method, and the one in the stack.
// ie we need to use RefCells to allow dynamic mutability. (We don't need Rc
// since none of those refs need actual ownership).
// - Use a ghost stack that keeps raw pointers to the nodes, bypassing the
// borrow checker, and implement a sane api to visit the stack.
//
// - Method 1 is doable but gives up on sibling-call optimization
// for insert, and yields some pretty terrible code.
// - Method 2 works fine for insertion but makes coding the Iterator
// a real pain. (Unless we're fine with giving the user a Ref<'a> instead
// of a &'a, which I'm not.)
// - Method 3 gives up on safety locally, but should be easier to implement
// and yield better performance than the two previous methods.
struct GhostStack<K, V> {
  priv inner: ~[*mut Node<K, V>],
}

struct StackAcc<'a, K, V> {
  priv inner: &'a mut ~[*mut Node<K, V>],
}

struct StackDec<'a, K, V> {
  priv inner: StackAcc<'a, K, V>,
}

impl<K: Ord, V> GhostStack<K, V> {
  #[inline(always)]
  fn new(initial_capacity: uint) -> GhostStack<K, V> {
    GhostStack {
      inner: std::vec::with_capacity(m_depth(initial_capacity)),
    }
  }

  #[inline(always)]
  fn get_acc<'a>(&'a mut self) -> StackAcc<'a, K, V> {
    StackAcc { inner: &mut self.inner }
  }
}

impl<'a, K: Ord, V> StackAcc<'a, K, V> {
  #[inline(always)]
  fn push_node(&mut self, n: &mut Node<K, V>) {
    self.inner.push(std::ptr::to_mut_unsafe_ptr(n));
  }

  fn to_dec(self) -> StackDec<'a, K, V> {
    StackDec { inner: self }
  }
}

#[unsafe_destructor]
impl<'a, K: Ord, V> Drop for StackAcc<'a, K, V> {
  fn drop(&mut self) {
    println!("dropped stack acc");
    self.inner.truncate(0);
  }
}

impl<'a, K: Ord, V> StackDec<'a, K, V> {
  #[inline]
  fn pop_node_opt<'b>(&'b mut self) -> Option<&'b mut Node<K, V>> {
    self.inner.inner.pop_opt().and_then(|raw_node| unsafe {
      std::cast::transmute(raw_node)
    })
  }
  #[inline]
  fn current<'b>(&'b self) -> Option<&'b Node<K, V>> {
    self.inner.inner.last_opt().and_then(|raw_node| unsafe {
      std::cast::transmute(raw_node)
    })
  }
  #[inline]
  fn parent<'b>(&'b self) -> Option<&'b Node<K, V>> {
    self.inner.inner.get_opt(self.inner.inner.len()-2).and_then(|raw_node| unsafe {
      std::cast::transmute(raw_node)
    })
  }
  #[inline]
  fn grandparent<'b>(&'b self) -> Option<&'b Node<K, V>> {
    self.inner.inner.get_opt(self.inner.inner.len()-3).and_then(|raw_node| unsafe {
      std::cast::transmute(raw_node)
    })
  }
  #[inline]
  fn uncle<'b>(&'b self) -> Option<&'b Node<K, V>> {
    let gp = self.grandparent().unwrap();
    let p = self.parent().unwrap();
    return if gp.left.is_none() {
      None
    } else if ptr_eq(&**gp.left.as_ref().unwrap(), p) {
      gp.left.as_ref().map(|r| &**r)
    } else {
      gp.right.as_ref().map(|r| &**r)
    }
  }
}

pub struct RbTree<K, V> {
  root: Option<~Node<K, V>>,
  len: uint,
  gstack: GhostStack<K, V>,
}

impl<K: Ord, V> RbTree<K, V> {
  /// Creates a new red-black tree.
  #[inline(always)]
  pub fn new() -> RbTree<K, V> {
    RbTree {
      root: None, len: 0, gstack: GhostStack::new(16),
    }
  }

  fn repaint<'a>(mut dec: StackDec<'a, K, V>) {
    // Case 2.
    if dec.parent().unwrap().color == Black {
      return;
    }
    if dec.uncle().unwrap().color == Red {
    // Case 3.
    } else {
    // Case 4.
    }
  }

  /// Insert a key-value pair in the tree and return true,
  /// or do nothing and return false if the key is already present.
  #[inline(always)]
  pub fn insert(&mut self, key: K, val: V) -> bool {
    self.root = match self.root.as_mut() {
      Some(node) => {
        let mut acc = self.gstack.get_acc();
        acc.push_node(&mut **node);
        return node.insert(key, val, &mut acc) && {
          self.len += 1;
          RbTree::repaint(acc.to_dec());
          true
        };
      }
      None => Some(~Node::new(key, val)),
    };
    true
  }

  #[inline(always)]
  pub fn iter<'a>(&'a self) -> RbTreeIterator<'a, K, V> {
    let mut iter = RbTreeIterator { stack: std::vec::with_capacity(m_depth(self.len)) };
    iter.push_left_tree(self.root.as_ref());
    iter
  }
}

pub struct RbTreeIterator<'a, K, V> {
  stack: ~[&'a Node<K, V>],
}

impl<'tree, K: Ord, V> RbTreeIterator<'tree, K, V> {
  #[inline(always)]
  fn push_left_tree(&mut self, root: Option<&'tree ~Node<K, V>>) {
    root.while_some(|node_ref| {
      self.stack.push(&**node_ref);
      node_ref.left.as_ref()
    });
  }

  #[inline(always)]
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
  let ordered = ["A", "B", "C", "D", "E", "F"];
  for ((_, v), expected) in rbt.iter().zip(ordered.iter()) {
    assert_eq!(v, expected);
  }
}

#[test]
fn test_search() {
}
