use crate::btree_node::{Node, B};
use std::cell::RefCell;
use std::marker::PhantomData;
use std::rc::Rc;

/// An iterator over the entries of a [`BTreeMap`].
///
/// This `struct` is created by the [`iter`] method on [`BTreeMap`]. See its
/// documentation for more.
///
/// [`iter`]: BTreeMap::iter
#[derive(Default)]
pub struct Iter<'a, K, V>
where
    K: Ord + Sized + Default,
    V: Sized + Default,
{
    pub(super) current: Option<Rc<RefCell<Node<K, V>>>>,
    // The index of current key/value pair in current node
    pub(super) current_idx: usize,
    pub(super) parent: Option<Box<Iter<'a, K, V>>>,
    // The index of current node in its parent's children array
    pub(super) parent_idx: usize,
    pub(super) return_from_child: [bool; B * 2 + 1],
    pub(super) marker: PhantomData<&'a V>,
}

impl<'a, K: 'a, V: 'a> Iterator for Iter<'a, K, V>
where
    K: Ord + Sized + Default,
    V: Sized + Default,
{
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        if self.current.is_none() && self.parent.is_none() {
            return None; // Stop the iteration
        }

        let current_idx = self.current_idx;
        let node = self.current.as_ref().unwrap().clone();
        let node = node.borrow();

        // If current element has unvisited child, then go down it first
        if !self.return_from_child[current_idx] && node.children[current_idx].is_some() {
            let child = (*node.children[current_idx].as_ref().unwrap()).clone();
            *self = Iter {
                current: Some(child),
                current_idx: 0,
                parent: Some(Box::new(std::mem::take(self))),
                parent_idx: current_idx,
                return_from_child: [false; B * 2 + 1],
                marker: PhantomData,
            };
            return self.next();
        } else {
            if current_idx < node.length as usize {
                let (item_k, item_v) = (&node.keys[current_idx], &node.values[current_idx]);
                let item_k = unsafe { &*(item_k as *const K as *const K) };
                let item_v = unsafe { &*(item_v as *const V as *const V) };
                self.current_idx += 1;
                return Some((item_k, item_v));
            } else {
                // If current node is done, try its parent
                match self.parent.take() {
                    Some(mut parent) => {
                        parent.current_idx = self.parent_idx;
                        parent.return_from_child[parent.current_idx] = true;
                        *self = *parent;
                        return self.next();
                    }
                    // If no parent, then stop the iteration.
                    None => return None,
                }
            }
        };
    }
}

/// A mutable iterator over the entries of a [`BTreeMap`].
///
/// This `struct` is created by the [`iter_mut`] method on [`BTreeMap`]. See its
/// documentation for more.
///
/// [`iter_mut`]: BTreeMap::iter_mut
#[derive(Default)]
pub struct IterMut<'a, K, V>
where
    K: Ord + Sized + Default,
    V: Sized + Default,
{
    pub(super) current: Option<Rc<RefCell<Node<K, V>>>>,
    pub(super) current_idx: usize,
    pub(super) parent: Option<Box<IterMut<'a, K, V>>>,
    pub(super) parent_idx: usize,
    pub(super) return_from_child: [bool; B * 2 + 1],
    pub(super) marker: PhantomData<&'a V>,
}

impl<'a, K, V> Iterator for IterMut<'a, K, V>
where
    K: Ord + Sized + Default + 'a,
    V: Sized + Default + 'a,
{
    type Item = (&'a K, &'a mut V);

    // This function is the same as the immutable one, except the mutability part.
    fn next(&mut self) -> Option<Self::Item> {
        if self.current.is_none() && self.parent.is_none() {
            return None;
        }

        let current_idx = self.current_idx;
        let node = self.current.as_ref().unwrap().clone();
        let node = node.borrow_mut();

        if !self.return_from_child[current_idx] && node.children[current_idx].is_some() {
            let child = (*node.children[current_idx].as_ref().unwrap()).clone();
            *self = IterMut {
                current: Some(child),
                current_idx: 0,
                parent: Some(Box::new(std::mem::take(self))),
                parent_idx: current_idx,
                return_from_child: [false; B * 2 + 1],
                marker: PhantomData,
            };
            return self.next();
        } else {
            if current_idx < node.length as usize {
                let (item_k, item_v) = (&node.keys[current_idx], &node.values[current_idx]);
                let item_k = unsafe { &*(item_k as *const K as *const K) };
                let item_v = unsafe { &mut *(item_v as *const V as *mut V) };
                self.current_idx += 1;
                return Some((item_k, item_v));
            } else {
                match self.parent.take() {
                    Some(mut parent) => {
                        parent.current_idx = self.parent_idx;
                        parent.return_from_child[parent.current_idx] = true;
                        *self = *parent;
                        return self.next();
                    }
                    None => return None,
                }
            }
        };
    }
}
