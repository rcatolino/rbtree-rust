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
      color: Black,
      data: val,
      key: key,
      left: None,
      right: None,
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

  fn insert(&mut self, key: K, val: V) -> bool {
    let child_opt = if key < self.key {
      &mut self.left
    } else if key > self.key {
      &mut self.right
    } else {
      return false;
    };

    *child_opt = match child_opt.as_mut() {
      None => Some(~Node::new(key, val)),
      // XXX check sibling call optimization.
      Some(child) => return child.insert(key, val),
    };
    true
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
      root: None,
      len: 0,
    }
  }

  /// Insert a key-value pair in the tree and return true,
  /// or do nothing and return false if the key is already present.
  pub fn insert(&mut self, key: K, val: V) -> bool {
    self.root = match self.root.as_mut() {
      Some(node) => return node.insert(key, val) && {self.len += 1; true},
      None => Some(~Node::new(key, val)),
    };
    true
  }

  pub fn iter<'a>(&'a self) -> RbTreeIterator<'a, K, V> {
    println!("depth {}", m_depth(self.len)); // XXX remove
    let mut iter = RbTreeIterator {
      stack: std::vec::with_capacity(m_depth(self.len)),
    };
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
  rbt.insert("key4", "D");
  rbt.insert("key2", "B");
  rbt.insert("key6", "F");
  rbt.insert("key3", "C");
}

#[test]
fn test_search() {
}
