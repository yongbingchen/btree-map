use std::borrow::Borrow;
use std::cell::{RefCell, RefMut};
use std::cmp::Ordering;
use std::mem::take;
use std::rc::Rc;

// #![feature(generic_const_exprs)] The generic_const_exprs feature is unstable, so use a const
// instead
#[cfg(feature = "sanity_test")]
pub(super) const B: usize = 3;
#[cfg(not(feature = "sanity_test"))]
pub(super) const B: usize = 6;
#[derive(Default)]
pub(super) struct Node<K, V>
where
    K: Ord + Sized + Default,
    V: Sized + Default,
{
    pub(super) keys: [K; B * 2],
    pub(super) values: [V; B * 2],
    pub(super) children: [Option<Rc<RefCell<Node<K, V>>>>; 2 * B + 1],
    // The number of keys and values this node stores.
    pub(super) length: u16,
}

pub(super) enum SearchResult<'a, V>
where
    V: Sized + Default,
{
    NotFound,
    Found(usize),
    GoDown(&'a V),
}

pub(super) enum InsertResult<K, V>
where
    K: Ord + Sized + Default,
    V: Sized + Default,
{
    NodeSplit(Node<K, V>),
    KeyExist(V),
    KeyNotExist(),
}

enum IndexResult {
    NotFound,
    Found(usize),
    GoDown(usize),
}

impl<K, V> Node<K, V>
where
    K: Ord + Sized + Default,
    V: Sized + Default,
{
    pub(super) fn new() -> Self {
        Default::default()
    }

    pub(super) fn search<'a, Q: ?Sized>(&'a self, key: &Q) -> SearchResult<'a, V>
    where
        K: Borrow<Q> + Ord,
        Q: Ord,
    {
        match self.find_key_index(key) {
            IndexResult::Found(index) => return SearchResult::Found(index),
            IndexResult::GoDown(index) => {
                return {
                    if self.children[index].is_some() {
                        let child = RefCell::borrow(&**self.children[index].as_ref().unwrap());
                        match child.search(key) {
                            SearchResult::Found(index) => {
                                return {
                                    SearchResult::GoDown(unsafe {
                                        &*(&child.values[index] as *const V as *const V)
                                    })
                                }
                            }
                            SearchResult::GoDown(value_ref) => {
                                return SearchResult::GoDown(unsafe {
                                    &*(value_ref as *const V as *const V)
                                })
                            }
                            SearchResult::NotFound => return SearchResult::NotFound,
                        }
                    }
                    SearchResult::NotFound
                }
            }
            IndexResult::NotFound => return SearchResult::NotFound,
        }
    }

    pub(super) fn add_recursive(&mut self, key: K, value: V) -> InsertResult<K, V>
    where
        K: Ord,
    {
        match &self.find_key_index(&key) {
            IndexResult::Found(pos) => {
                let old_v = take(&mut self.values[*pos]);
                self.values[*pos] = value;
                return InsertResult::KeyExist(old_v);
            }
            IndexResult::NotFound => {
                // key is greater than all self.keys, add it to the last slot
                return self.do_add_recursive(key, value, self.keys.len());
            }
            IndexResult::GoDown(pos) => {
                return self.do_add_recursive(key, value, *pos);
            }
        }
    }

    fn do_add_recursive(&mut self, key: K, value: V, pos: usize) -> InsertResult<K, V> {
        if self.children[pos].as_ref().is_none() {
            // No left child at insert position, by definition this is a leaf node,
            // just insert it to this node, then maybe split it later
            self.insert(key, value);
            return self.split(InsertResult::KeyNotExist());
        };

        let ret;
        {
            let child = (*self.children[pos].as_ref().unwrap()).clone();
            let mut child = child.borrow_mut();
            ret = match child.add_recursive(key, value) {
                InsertResult::KeyNotExist() => InsertResult::KeyNotExist(),
                InsertResult::KeyExist(v) => InsertResult::KeyExist(v),
                InsertResult::NodeSplit(mut w) => {
                    // Child was split, w is the new child node (the original child is still
                    // valid). Promote the largest element in the new child (the smaller
                    // group) to its parent, to makes a slot in its parent to hold this new
                    // child
                    let (x_k, x_v) = w.remove(B - 1);
                    self.insert(x_k, x_v);
                    self.add_child(Some(Rc::new(RefCell::new(w))), pos);
                    InsertResult::KeyNotExist()
                }
            };
        }
        return self.split(ret);
    }

    // Internal function, skip check for out of range
    pub(super) fn remove(&mut self, pos: usize) -> (K, V) {
        // Use take/replace/swap to manipulate field behind mutable borrow
        let ret = (take(&mut self.keys[pos]), take(&mut self.values[pos]));
        for i in pos..self.length as usize - 1 {
            // let (left, right) = self.keys.split_array_mut::<{i}>(); // is unstable
            let right_k = take(&mut self.keys[i + 1]);
            let right_v = take(&mut self.values[i + 1]);
            self.keys[i] = right_k;
            self.values[i] = right_v;
        }

        self.length -= 1;
        return ret;
    }

    pub(super) fn erase_recursive<Q: ?Sized>(&mut self, key: &Q) -> Option<V>
    where
        K: Borrow<Q> + Ord,
        Q: Ord,
    {
        match &self.find_key_index(&key) {
            IndexResult::Found(pos) => {
                let (_, old_v) = self.remove(*pos);
                if !self.is_leaf() {
                    let (borrow_k, borrow_v);
                    // Borrow one from its child to keep the tree structure.
                    // This pair of curly brackets is for limiting lifetime of the child's mutable borrow.
                    {
                        let child = (*self.children[pos + 1].as_ref().unwrap()).clone();
                        let mut child = child.borrow_mut();
                        (borrow_k, borrow_v) = child.remove_smallest();
                    }
                    self.insert(borrow_k, borrow_v);
                    self.check_child_underflow(pos + 1);
                }
                return Some(old_v);
            }
            IndexResult::NotFound => {
                // key is greater than all self.keys, erase the last slot
                return self.do_erase_recursive(key, self.keys.len());
            }
            IndexResult::GoDown(pos) => {
                return self.do_erase_recursive(key, *pos);
            }
        }
    }

    fn do_erase_recursive<Q: ?Sized>(&mut self, key: &Q, pos: usize) -> Option<V>
    where
        K: Borrow<Q> + Ord,
        Q: Ord,
    {
        if self.children[pos].is_some() {
            let ret;
            {
                let child = (*self.children[pos].as_ref().unwrap()).clone();
                let mut child = child.borrow_mut();
                ret = child.erase_recursive(key);
            }
            self.check_child_underflow(pos);
            return ret;
        }
        None
    }

    #[allow(unused_assignments)]
    fn remove_smallest(&mut self) -> (K, V) {
        if self.is_leaf() {
            return self.remove(0);
        }

        let mut ret = Default::default();
        {
            let child = (*self.children[0].as_ref().unwrap()).clone();
            let mut child = child.borrow_mut();
            ret = child.remove_smallest();
        }
        self.check_child_underflow(0);
        return ret;
    }

    // Whenever an element is removed from a child, need to check if it's
    // underflow, and perform tree re-balance if needed.
    fn check_child_underflow(&mut self, child_idx: usize) {
        if self.children[child_idx].is_none() {
            return;
        }

        let child = (*self.children[child_idx].as_ref().unwrap()).clone();
        let child = child.borrow_mut();

        if (child.length as usize) < B - 1 {
            // Child node underflow
            let has_left_sibling = child_idx != 0;
            let has_right_sibling = child_idx < 2 * B && self.children[child_idx + 1].is_some();

            // Prefer merge over borrow
            if has_left_sibling {
                let left_sibling = (*self.children[child_idx - 1].as_ref().unwrap()).clone();
                let left_sibling = left_sibling.borrow_mut();
                if (left_sibling.length as usize) <= B {
                    self.merge(child_idx - 1, left_sibling, child);
                    return;
                }
            }
            if has_right_sibling {
                let right_sibling = (*self.children[child_idx + 1].as_ref().unwrap()).clone();
                let right_sibling = right_sibling.borrow_mut();
                if (right_sibling.length as usize) <= B {
                    self.merge(child_idx, child, right_sibling);
                    return;
                }
            }

            // Awkward duplicated code, for Rust scope rule
            if has_left_sibling {
                let left_sibling = (*self.children[child_idx - 1].as_ref().unwrap()).clone();
                let left_sibling = left_sibling.borrow_mut();
                self.borrow_from_left(child_idx, child, left_sibling);
                return;
            }
            if has_right_sibling {
                let right_sibling = (*self.children[child_idx + 1].as_ref().unwrap()).clone();
                let right_sibling = right_sibling.borrow_mut();
                self.borrow_from_right(child_idx, child, right_sibling);
                return;
            }
        }
    }

    // Merge right_child to its left sibling, and let parent->children[child_idx]
    // point to the merged node
    fn merge(
        &mut self,
        merge_to_idx: usize,
        mut left_child: RefMut<Node<K, V>>,
        mut right_child: RefMut<Node<K, V>>,
    ) {
        // Merge cause parent to lose one child, remove one element to make room for
        // it.
        let (e_k, e_v) = self.remove(merge_to_idx);
        left_child.insert(e_k, e_v);
        let right_child_size = right_child.length as usize;
        let mut i = left_child.length as usize;
        for j in 0..right_child_size {
            left_child.keys[i] = take(&mut right_child.keys[j]);
            left_child.values[i] = take(&mut right_child.values[j]);
            left_child.children[i] = take(&mut right_child.children[j]);
            i += 1;
        }
        let left_child_size = left_child.length as usize + right_child_size;
        left_child.children[left_child_size] = take(&mut right_child.children[right_child_size]);
        left_child.length = left_child_size as u16;

        // Move all other right children ahead one slot, implictly release the
        // right_child node.
        for i in merge_to_idx + 1..B * 2 {
            self.children[i] = take(&mut self.children[i + 1]);
        }
    }

    fn borrow_from_left(
        &mut self,
        child_idx: usize,
        mut child: RefMut<Node<K, V>>,
        mut left_sibling: RefMut<Node<K, V>>,
    ) {
        let last = (left_sibling.length as usize) - 1;
        let (e_k, e_v) = left_sibling.remove(last);
        let (p_k, p_v) = self.remove(child_idx - 1);
        self.insert(e_k, e_v);
        child.insert(p_k, p_v);
        // Move the last child of left_sibling as the first child of the right node
        let l_child = left_sibling.remove_child(last + 1);
        child.add_child(l_child, 0);
    }

    fn borrow_from_right(
        &mut self,
        child_idx: usize,
        mut child: RefMut<Node<K, V>>,
        mut right_sibling: RefMut<Node<K, V>>,
    ) {
        let (e_k, e_v) = right_sibling.remove(0);
        let (p_k, p_v) = self.remove(child_idx);
        self.insert(e_k, e_v);
        child.insert(p_k, p_v);
        // Move the first child of right_sibling as the last child of left node
        let r_child = right_sibling.remove_child(0);
        let last = child.length as usize;
        child.add_child(r_child, last);
    }

    fn is_leaf(&self) -> bool {
        self.children[0].is_none()
    }

    // Split a node to two, if its elements number is 2B
    // After split, the new node will hold first B elements, and the remaining B
    // elements will be in the original node. The new node will be returned after
    // split.
    fn split(&mut self, ret: InsertResult<K, V>) -> InsertResult<K, V> {
        if (self.length as usize) < 2 * B {
            return ret;
        }

        let mut new_child: Node<K, V> = Node::new();
        for i in 0..B {
            new_child.keys[i] = take(&mut self.keys[i]);
            new_child.values[i] = take(&mut self.values[i]);
            new_child.children[i] = take(&mut self.children[i]);
        }
        new_child.length = B as u16;
        // Last element of a non-leaf node is allowed to have empty right child
        new_child.children[B] = None;

        for i in 0..B {
            self.keys[i] = take(&mut self.keys[i + B]);
            self.values[i] = take(&mut self.values[i + B]);
            self.children[i] = take(&mut self.children[i + B]);
        }
        self.length = B as u16;
        self.children[B] = take(&mut self.children[B * 2]);
        InsertResult::NodeSplit(new_child)
    }

    // This is always called after insert()
    fn add_child(&mut self, new_child: Option<Rc<RefCell<Node<K, V>>>>, pos: usize) {
        for i in (pos..self.length as usize).rev() {
            let left_child = take(&mut self.children[i]);
            self.children[i + 1] = left_child;
        }
        self.children[pos] = new_child;
    }

    // This is always called after remove()
    fn remove_child(&mut self, pos: usize) -> Option<Rc<RefCell<Node<K, V>>>> {
        let ret = take(&mut self.children[pos]);
        for i in pos..self.length as usize + 1 {
            self.children[i] = take(&mut self.children[i + 1]);
        }
        ret
    }

    // Insert operation allows to increase node's total elements to 2B: will then
    // follow with a split
    fn insert(&mut self, key: K, value: V)
    where
        K: Ord,
    {
        for pos in 0..self.keys.len() {
            match key.cmp(self.keys[pos].borrow()) {
                Ordering::Greater => {
                    if pos == self.length as usize {
                        self.insert_at(key, value, pos);
                        break;
                    }
                }
                Ordering::Equal => {
                    if pos == self.length as usize {
                        // This happens only when key equals to default
                        self.insert_at(key, value, pos);
                        break;
                    }
                }
                Ordering::Less => {
                    self.insert_at(key, value, pos);
                    break;
                }
            }
        }
        self.length += 1;
    }

    fn insert_at(&mut self, key: K, value: V, pos: usize) {
        for i in (pos..self.length as usize).rev() {
            let left_k = take(&mut self.keys[i]);
            let left_v = take(&mut self.values[i]);
            self.keys[i + 1] = left_k;
            self.values[i + 1] = left_v;
        }
        self.keys[pos] = key;
        self.values[pos] = value;
    }

    fn find_key_index<'a, Q: ?Sized>(&'a self, key: &Q) -> IndexResult
    where
        Q: Ord,
        K: Borrow<Q>,
    {
        for i in 0..self.length as usize {
            match key.cmp(self.keys[i].borrow()) {
                Ordering::Greater => {
                    if i == self.length as usize - 1 && self.children[i + 1].is_some() {
                        return IndexResult::GoDown(i + 1);
                    }
                }
                Ordering::Equal => return IndexResult::Found(i),
                Ordering::Less => {
                    if self.children[i].is_some() {
                        return IndexResult::GoDown(i);
                    }
                }
            }
        }
        // key is greater than all self.keys
        IndexResult::NotFound
    }

    #[cfg(test)]
    pub(super) fn bfs(&self, layer: usize, result: &mut Vec<Vec<Vec<(K, V)>>>)
    where
        K: Clone,
        V: Clone,
    {
        if self.length == 0 {
            return;
        }

        let mut node: Vec<(K, V)> = Default::default();
        for i in 0..self.length as usize {
            node.push((self.keys[i].clone(), self.values[i].clone()));
        }

        if result.len() > layer {
            result[layer].push(node);
        } else {
            let mut l: Vec<Vec<(K, V)>> = Default::default();
            l.push(node);
            result.push(l);
        }

        for i in 0..self.length as usize + 1 {
            if self.children[i].is_some() {
                RefCell::borrow(&**self.children[i].as_ref().unwrap()).bfs(layer + 1, result);
            }
        }
    }
}
