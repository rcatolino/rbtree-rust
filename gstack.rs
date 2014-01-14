use super::{Child, Left, Right, Black, Red, No, LRotate, RRotate,
            NeedsRotation, Node, m_depth, ptr_eq};
use std::vec::with_capacity;
use std::ptr::to_mut_unsafe_ptr;
// What is this? :
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
pub struct GhostStack<K, V> {
  priv inner: ~[*mut Node<K, V>],
}

pub struct StackAcc<'a, K, V> {
  priv inner: &'a mut ~[*mut Node<K, V>],
}

pub struct StackDec<'a, K, V> {
  priv inner: StackAcc<'a, K, V>,
}

impl<K: Ord, V> GhostStack<K, V> {
  #[inline(always)]
  pub fn new(initial_capacity: uint) -> GhostStack<K, V> {
    GhostStack {
      inner: with_capacity(m_depth(initial_capacity)),
    }
  }

  #[inline(always)]
  pub fn get_acc<'a>(&'a mut self) -> StackAcc<'a, K, V> {
    StackAcc { inner: &mut self.inner }
  }
}

impl<'a, K: Ord, V> StackAcc<'a, K, V> {
  #[inline(always)]
  pub fn push_node(&mut self, n: &mut Node<K, V>) {
    self.inner.push(to_mut_unsafe_ptr(n));
  }

  pub fn to_dec(self) -> StackDec<'a, K, V> {
    StackDec { inner: self }
  }
}

#[unsafe_destructor]
impl<'a, K: Ord, V> Drop for StackAcc<'a, K, V> {
  fn drop(&mut self) {
    self.inner.truncate(0);
  }
}

impl<'a, K: Ord, V> StackDec<'a, K, V> {
  #[inline]
  fn shorten<'b>(&'b mut self, how_much: uint) {
    let new_len = self.inner.inner.len() - how_much;
    self.inner.inner.truncate(new_len);
  }
  #[inline]
  fn current<'b>(&'b mut self) -> Option<&'b mut Node<K, V>> {
    self.inner.inner.last_opt().map(|raw_node| unsafe {
      &mut **raw_node
    })
  }
  #[inline]
  // Fails if current has no parent!
  fn current_side<'b>(&'b self) -> Child {
    let c: &'b Node<K, V> = self.inner.inner.last_opt().map(|raw_node| unsafe {
      &mut **raw_node
    }).unwrap();
    let p = self.parent().unwrap();
    return if p.left.is_some() && ptr_eq(&**p.left.as_ref().unwrap(), c) {
      Left
    } else {
      Right
    }
  }

  #[inline]
  fn parent<'b>(&'b self) -> Option<&'b Node<K, V>> {
    self.inner.inner.get_opt(self.inner.inner.len()-2).map(|raw_node| unsafe {
      &**raw_node
    })
  }
  #[inline]
  fn grandparent<'b>(&'b self) -> Option<&'b Node<K, V>> {
    self.inner.inner.get_opt(self.inner.inner.len()-3).map(|raw_node| unsafe {
      &**raw_node
    })
  }
  // Fails if current has no parent/grandparent!
  #[inline]
  fn uncle<'b>(&'b self) -> (Child, Option<&'b Node<K, V>>) {
    let gp = self.grandparent().unwrap();
    let p = self.parent().unwrap();
    return if gp.left.is_none() {
      (Left, None)
    } else if ptr_eq(&**gp.left.as_ref().unwrap(), p) {
      (Right, gp.right.as_ref().map(|r| &**r))
    } else {
      (Left, gp.left.as_ref().map(|r| &**r))
    }
  }

  pub fn repaint(mut self) -> NeedsRotation {
    // Case 1.
    if self.parent().is_none() {
      self.current().unwrap().color = Black;
      return No;
    }
    // Case 2.
    if self.parent().unwrap().color == Black {
      return No;
    }
    // Uncle's side and color :
    let (uncle_side, is_red) = match self.uncle() {
      (side, uncle) => (side, uncle.map_or(false, |u| u.color == Red))
    };
    if is_red {
      // Case 3.
      {
        let gp = {self.shorten(2); self.current().unwrap()};
        gp.color = Red;
        gp.left.as_mut().unwrap().color = Black;
        gp.right.as_mut().unwrap().color = Black;
      }
      return self.repaint();
    } else {
      // Case 4.
      let mut current_side = self.current_side();
      {
        let gp = {self.shorten(2); self.current().unwrap()};
        if uncle_side == Right && current_side == Right {
          gp.lrotate(Left) || fail!("left rotate failed");
          current_side = Left;
        } else if uncle_side == Left && current_side == Left {
          gp.rrotate(Right) || fail!("left rotate failed");
          current_side = Right;
        }
        // Now both parent and current are on the same side.
        // Flip parent and grand parent colors :
        // We know that grand-parent was black, otherwise parent would have been
        // and we would have stopped on case 2.
        gp.color = Red;
        if current_side == Left {
          // Simmilarly we know that parent's color was red.
          gp.left.as_mut().unwrap().color = Black;
        } else {
          gp.right.as_mut().unwrap().color = Black;
        }
      }
      if self.parent().is_some() {
        let gp_side = self.current_side();
        let ggp = {self.shorten(1); self.current().unwrap()};
        if current_side == Left {
          ggp.rrotate(gp_side) || fail!("left rotate failed");
        } else {
          ggp.lrotate(gp_side) || fail!("left rotate failed");
        }
        return No;
      // We can't rotate the root because we have no ref to it,
      // so we ask the parent to do it if needed.
      } else if current_side == Left {
        return RRotate;
      } else {
        return LRotate;
      }
    }
  }
}


