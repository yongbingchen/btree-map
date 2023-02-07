//! My rust practice project, a B-Tree Map implementation.
//! The B-Tree Map interface definition is copied from [rust std library](https://github.com/rust-lang/rust.git), commit
//! 69f9c33d71c871fc16ac445211281c6e7a340943, library/alloc/src/collections/btree/map.rs.
//! The Rust Project is dual-licensed under Apache 2.0 and MIT, see its [COPYRIGHT](https://github.com/rust-lang/rust/blob/master/COPYRIGHT)

#![warn(missing_docs)]

use std::cell::RefCell;
use std::rc::Rc;
use std::borrow::Borrow;
use std::marker::PhantomData;
use std::fmt;

mod btree_node;
use btree_node::{Node, SearchResult, InsertResult, B};

mod btree_iter;
use btree_iter::{Iter, IterMut};

/// An ordered map based on a [B-Tree].
///
/// B-Trees represent a fundamental compromise between cache-efficiency and actually minimizing
/// the amount of work performed in a search. In theory, a binary search tree (BST) is the optimal
/// choice for a sorted map, as a perfectly balanced BST performs the theoretical minimum amount of
/// comparisons necessary to find an element (log<sub>2</sub>n). However, in practice the way this
/// is done is *very* inefficient for modern computer architectures. In particular, every element
/// is stored in its own individually heap-allocated node. This means that every single insertion
/// triggers a heap-allocation, and every single comparison should be a cache-miss. Since these
/// are both notably expensive things to do in practice, we are forced to at very least reconsider
/// the BST strategy.
///
/// A B-Tree instead makes each node contain B-1 to 2B-1 elements in a contiguous array. By doing
/// this, we reduce the number of allocations by a factor of B, and improve cache efficiency in
/// searches. However, this does mean that searches will have to do *more* comparisons on average.
/// The precise number of comparisons depends on the node search strategy used. For optimal cache
/// efficiency, one could search the nodes linearly. For optimal comparisons, one could search
/// the node using binary search. As a compromise, one could also perform a linear search
/// that initially only checks every i<sup>th</sup> element for some choice of i.
///
/// Iterators obtained from functions such as [`BTreeMap::iter`], or [`BTreeMap::iter_mut`],
/// produce their items in order by key, and take worst-case logarithmic and amortized constant
/// time per item returned.
///
/// [B-Tree]: https://en.wikipedia.org/wiki/B-tree
///
/// # Examples
///
/// ```
/// use btree_map::BTreeMap;
///
/// // type inference lets us omit an explicit type signature (which
/// // would be `BTreeMap<&str, &str>` in this example).
/// let mut movie_reviews = BTreeMap::new();
///
/// // review some movies.
/// movie_reviews.insert("Office Space",       "Deals with real issues in the workplace.");
/// movie_reviews.insert("Pulp Fiction",       "Masterpiece.");
/// movie_reviews.insert("The Godfather",      "Very enjoyable.");
/// movie_reviews.insert("The Blues Brothers", "Eye lyked it a lot.");
///
/// // check for a specific one.
/// if None == movie_reviews.get("Les Misérables") {
///     println!("We've got some reviews, but Les Misérables ain't one.");
/// }
///
/// // oops, this review has a lot of spelling mistakes, let's delete it.
/// movie_reviews.remove("The Blues Brothers");
///
/// // This can't compile, in-place mutation is invalid for type &str
/// // if let mut_review = movie_reviews.get_mut("Pulp Fiction") {
/// //     *mut_review = " This is really enjoyable.";
/// // }
///
/// // look up the values associated with some keys.
/// let to_find = ["Up!", "Office Space"];
/// for movie in &to_find {
///     match movie_reviews.get(movie) {
///         Some(review) => println!("{movie}: {review}"),
///         None => println!("{movie} is unreviewed.")
///     }
/// }
///
/// // iterate over everything, do some in-place mutation.
/// for (movie, review) in &mut movie_reviews {
///     if movie != &"Office Space" {
///         *review = "It is great, but it's not Office Space.";
///     }
/// }
///
/// for (movie, review) in movie_reviews.iter() {
///     println!("{movie}: \"{review}\"");
/// }
///
/// let (first_movie, first_review) = movie_reviews.iter().next().unwrap();
/// assert_eq!((*first_movie, *first_review), ("Office Space", "Deals with real issues in the workplace."));
/// ```
#[derive(Default)]
pub struct BTreeMap<K, V>
where
    K: Ord + Sized + Default + fmt::Debug,
	V: Sized + Default + fmt::Debug,
{
    // Why not use exclusive Box? Because the node (and the value inside it) need to be borrowed
    // for iteration
    root: Option<Rc<RefCell<Node<K, V>>>>,
    length: usize,
}

impl <K, V> BTreeMap<K, V>
where
    K: Ord + Sized + Default + fmt::Debug,
	V: Sized + Default + fmt::Debug,
{
    pub fn new() -> Self {
        Default::default()
    }

    /// Returns a reference to the value corresponding to the key.
    ///
    /// The key may be any borrowed form of the map's key type, but the ordering
    /// on the borrowed form *must* match the ordering on the key type.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use btree_map::BTreeMap;
    ///
    /// let mut map = BTreeMap::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.get(&1), Some(&"a"));
    /// assert_eq!(map.get(&2), None);
    /// ```
    pub fn get<Q: ?Sized>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q> + Ord,
        Q: Ord,
    {
        if self.root.is_some() {
            let root = RefCell::borrow(&**self.root.as_ref().unwrap());
            let result = root.search(key);
            match result {
                SearchResult::NotFound => return None,
                SearchResult::Found(index) => return {
                    let ret = &root.values[index];
                    // SAFETY: return a reference to something locally borrowed is not possible under
                    // Rust borrow-checker rule, even though I know that the returned reference must have satisfied
                    // the lifetime parameter in the function signature, that it lives as long as the tree itself.
                    // In this case, use unsafe to take the responsibilities to uphold Rust's safety guarantees myself.
                    // See https://users.rust-lang.org/t/how-to-return-reference-to-value-in-rc-or-refcell/76729/18
                    // for more detailed explaination.
                    Some(unsafe { &*(ret as *const V as *const V) }) },
                SearchResult::GoDown(value_ref) => return Some( unsafe { &*(value_ref as *const V as *const V) }),
            };
        }
        None
    }

    /// Returns a mutable reference to the value corresponding to the key.
    ///
    /// The key may be any borrowed form of the map's key type, but the ordering
    /// on the borrowed form *must* match the ordering on the key type.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use btree_map::BTreeMap;
    ///
    /// let mut map = BTreeMap::new();
    /// map.insert(1, "a");
    /// if let Some(x) = map.get_mut(&1) {
    ///     *x = "b";
    /// }
    /// assert_eq!(map.get(&1), Some(&"b"));
    /// ```
    pub fn get_mut<Q: ?Sized>(&mut self, key: &Q) -> Option<&mut V>
    where
        K: Borrow<Q> + Ord,
        Q: Ord,
    {
        None
    }

    /// Inserts a key-value pair into the map.
    ///
    /// If the map did not have this key present, `None` is returned.
    ///
    /// If the map did have this key present, the value is updated, and the old
    /// value is returned. The key is not updated, though; this matters for
    /// types that can be `==` without being identical. See the [module-level
    /// documentation] for more.
    ///
    /// [module-level documentation]: index.html#insert-and-complex-keys
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use btree_map::BTreeMap;
    ///
    /// let mut map = BTreeMap::new();
    /// assert_eq!(map.insert(37, "a"), None);
    /// assert_eq!(map.get(&37), Some(&"a"));
    ///
    /// map.insert(37, "b");
    /// assert_eq!(map.insert(37, "c"), Some("b"));
    /// assert_eq!(map.get(&37), Some(&"c"));
    /// ```
    pub fn insert(&mut self, key: K, value: V) -> Option<V>
    where
        K: Ord,
    {
        if self.root.is_none() {
            self.root = Some(Rc::new(RefCell::new(Node::new())));
        }

        // Clone root because we may need to update it inside the block
        let root = (*self.root.as_ref().unwrap()).clone();
        let mut root = root.borrow_mut();
        let ret = match root.add_recursive(key, value) {
            InsertResult::KeyNotExist() => None,
            InsertResult::KeyExist(v) => Some(v),
            InsertResult::NodeSplit(mut new_node) => {
                let mut new_root = Node::new();
                let (root_k, root_v) = new_node.remove(B - 1);
                new_root.keys[0] = root_k;
                new_root.values[0] = root_v;
                new_root.children[0] = Some(Rc::new(RefCell::new(new_node)));
                new_root.children[1] = Some(self.root.as_ref().unwrap().clone());
                new_root.length = 1;
                self.root = Some(Rc::new(RefCell::new(new_root)));
                None
            },
        };

        self.length += 1;
        ret
    }

    /// Removes a key from the map, returning the value at the key if the key
    /// was previously in the map.
    ///
    /// The key may be any borrowed form of the map's key type, but the ordering
    /// on the borrowed form *must* match the ordering on the key type.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use btree_map::BTreeMap;
    ///
    /// let mut map = BTreeMap::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.remove(&1), Some("a"));
    /// assert_eq!(map.remove(&1), None);
    /// ```
    pub fn remove<Q: ?Sized>(&mut self, key: &Q) -> Option<V>
    where
        K: Borrow<Q> + Ord,
        Q: Ord,
    {
        if self.root.is_none() {
            return None;
        }
        let root = (*self.root.as_ref().unwrap()).clone();
        let mut root = root.borrow_mut();
        let ret = root.erase_recursive(key);

        // If the root is empty after erase, use its first (and should be the only)
        // child as new root
        if root.length == 0 && root.children[0].is_some() {
            self.root = std::mem::take(&mut root.children[0]);
        }
        self.length -= 1;
        return ret;
    }

    /// Gets an iterator over the entries of the map, sorted by key.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use btree_map::BTreeMap;
    ///
    /// let mut map = BTreeMap::new();
    /// map.insert(3, "c");
    /// map.insert(2, "b");
    /// map.insert(1, "a");
    ///
    /// for (key, value) in map.iter() {
    ///     println!("{key}: {value}");
    /// }
    ///
    /// let (first_key, first_value) = map.iter().next().unwrap();
    /// assert_eq!((*first_key, *first_value), (1, "a"));
    /// ```
    pub fn iter(&self) -> Iter<'_, K, V> {
        if self.root.is_some() {
            let root = (*self.root.as_ref().unwrap()).clone();
            Iter {
                current: Some(root),
                parent: None,
                current_idx: 0,
                parent_idx: 0,
                return_from_child: [false; B * 2 + 1],
                marker: PhantomData,
            }
        } else {
            Default::default()
        }
    }

    /// Gets a mutable iterator over the entries of the map, sorted by key.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use btree_map::BTreeMap;
    ///
    /// let mut map = BTreeMap::new();
    /// map.insert("a", 1);
    /// map.insert("b", 2);
    /// map.insert("c", 3);
    ///
    /// // add 10 to the value if the key isn't "a"
    /// for (key, value) in map.iter_mut() {
    ///     if key != &"a" {
    ///         *value += 10;
    ///     }
    /// }
    /// ```
    pub fn iter_mut(&mut self) -> IterMut<'_, K, V> {
        Default::default()
    }

    #[cfg(test)]
    pub fn bfs(&self, result: &mut Vec<Vec<Vec<(K, V)>>>)
    where
        K: Clone,
        V: Clone,
    {

        if self.root.as_ref().is_none() {
            return;
        }
        RefCell::borrow(&**self.root.as_ref().unwrap()).bfs(0, result);
    }
}

/// By implement IntoIterator, you define how a struct will be converted to an iterator.
/// This is required for the "for (key, value) in &mut map {} ", which is the idiomatic way
/// to use a mut iter.
impl<'a, K: Default + Ord + fmt::Debug, V: Default + fmt::Debug> IntoIterator for &'a mut BTreeMap<K, V> {
    type Item = (&'a K, &'a mut V);
    type IntoIter = IterMut<'a, K, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn check_btree_correctness(map: &BTreeMap::<i32, String>, expected_keys: Vec<Vec<Vec<i32>>>) {
        let mut result: Vec<Vec<Vec<(i32, String)>>> = Default::default();
        map.bfs(&mut result);

        for i in 0..result.len() {
            assert_eq!(expected_keys[i].len(), result[i].len());
            for j in 0..result[i].len() {
                assert_eq!(expected_keys[i][j].len(), result[i][j].len());
                for k in 0..result[i][j].len() {
                    assert_eq!(expected_keys[i][j][k], result[i][j][k].0);
                    assert_eq!((expected_keys[i][j][k] + 1).to_string(), result[i][j][k].1);
                }
            }
        }
    }

    fn print_btree(map: &BTreeMap::<i32, String>) {
        let mut result: Vec<Vec<Vec<(i32, String)>>> = Default::default();
        map.bfs(&mut result);
        for i in 0..result.len() {
            println!("At layer {}", &i);
            print!("[ ");
            for j in 0..result[i].len() {
                print!("[ ");
                for k in 0..result[i][j].len() {
                    print!("{:#?}, ", &result[i][j][k].0);
                }
                print!("] ");
            }
            println!(" ]");
        }
    }

    #[test]
    fn algorithm_coverage_tests() {
        println!("Please manually change B in src/lib/btree_node.rs to 3 before this algorithm_coverage_tests");
        let mut map = BTreeMap::<i32, String>::new();

        for j in 0..B * 2 {
            for i in 0..10 {
                map.insert((i * (B * 2 - 1) + j) as i32, (i * (B * 2 - 1) + j + 1).to_string());
            }
        }

        print_btree(&map);

        let expected_keys  = vec![
            vec![ vec![15, 31], ],
            vec![ vec![2, 5, 10], vec![18, 21, 25], vec![35, 40, 43, 46], ],
            vec![ vec![0, 1], vec![3, 4], vec![6, 7, 8, 9], vec![11, 12, 13, 14], vec![16, 17], vec![19, 20], vec![22, 23, 24], vec![26, 27, 28, 29, 30], vec![32, 33, 34], vec![36, 37, 38, 39], vec![41, 42], vec![44, 45], vec![47, 48, 49, 50], ],
        ];

        check_btree_correctness(&map, expected_keys);

        // Erase key '44' will cause its node to merge with its left sibling
        let mut v = map.remove(&44);
        assert!(v != None && *(v.unwrap()) == (44 + 1).to_string());
        let expected_keys_1 = vec![
            vec![ vec![15, 31], ],
            vec![ vec![2, 5, 10], vec![18, 21, 25], vec![35, 40, 46], ],
            vec![ vec![0, 1], vec![3, 4], vec![6, 7, 8, 9], vec![11, 12, 13, 14], vec![16, 17], vec![19, 20], vec![22, 23, 24], vec![26, 27, 28, 29, 30], vec![32, 33, 34], vec![36, 37, 38, 39], vec![41, 42, 43, 45], vec![47, 48, 49, 50], ],
        ];
        check_btree_correctness(&map, expected_keys_1);

        // Erase key '19' will cause its node to merge with its left sibling
        v = map.remove(&19);
        assert!(v != None && *(v.unwrap()) == (19 + 1).to_string());
        let expected_keys_2 = vec![
            vec![ vec![15, 31], ],
            vec![ vec![2, 5, 10], vec![21, 25], vec![35, 40, 46], ],
            vec![ vec![0, 1], vec![3, 4], vec![6, 7, 8, 9], vec![11, 12, 13, 14], vec![16, 17, 18, 20], vec![22, 23, 24], vec![26, 27, 28, 29, 30], vec![32, 33, 34], vec![36, 37, 38, 39], vec![41, 42, 43, 45], vec![47, 48, 49, 50], ],
        ];
        check_btree_correctness(&map, expected_keys_2);

        map.remove(&42);
        map.remove(&43);

        // Erase key '45' now will cause its node to borrow one element from its left
        // sibling
        v = map.remove(&45);
        assert!(v != None && *(v.unwrap()) == (45 + 1).to_string());
        let expected_keys_3 = vec![
            vec![ vec![15, 31], ],
            vec![ vec![2, 5, 10], vec![21, 25], vec![35, 39, 46], ],
            vec![ vec![0, 1], vec![3, 4], vec![6, 7, 8, 9], vec![11, 12, 13, 14], vec![16, 17, 18, 20], vec![22, 23, 24], vec![26, 27, 28, 29, 30], vec![32, 33, 34], vec![36, 37, 38], vec![40, 41], vec![47, 48, 49, 50], ],
        ];
        check_btree_correctness(&map, expected_keys_3);

        map.remove(&18);
        map.remove(&20);

        // Erase key '16' now will cause its node to merge to its right sibling, then
        // trigger its parent node to merge to its left sibling
        v = map.remove(&16);
        assert!(v != None && *(v.unwrap()) == (16 + 1).to_string());
        let expected_keys_4 = vec![
            vec![ vec![31], ],
            vec![ vec![2, 5, 10, 15, 25], vec![35, 39, 46], ],
            vec![ vec![0, 1], vec![3, 4], vec![6, 7, 8, 9], vec![11, 12, 13, 14], vec![17, 21, 22, 23, 24], vec![26, 27, 28, 29, 30], vec![32, 33, 34], vec![36, 37, 38], vec![40, 41], vec![47, 48, 49, 50], ],
        ];
        check_btree_correctness(&map, expected_keys_4);

        // Erase key '39' now will cause it to borrow element 40 from its child node,
        // then in turn it triggers this child node to merge to its left sibling.
        v = map.remove(&39);
        assert!(v != None && *(v.unwrap()) == (39 + 1).to_string());
        let expected_keys_5 = vec![
            vec![ vec![31], ],
            vec![ vec![2, 5, 10, 15, 25], vec![35, 46], ],
            vec![ vec![0, 1], vec![3, 4], vec![6, 7, 8, 9], vec![11, 12, 13, 14], vec![17, 21, 22, 23, 24], vec![26, 27, 28, 29, 30], vec![32, 33, 34], vec![36, 37, 38, 40, 41], vec![47, 48, 49, 50], ],
        ];
        check_btree_correctness(&map, expected_keys_5);

        // Erase key '0' now will cause its node to merge to its left sibling
        v = map.remove(&3);
        assert!(v != None && *(v.unwrap()) == (3 + 1).to_string());
        let expected_keys_6 = vec![
            vec![ vec![31], ],
            vec![ vec![5, 10, 15, 25], vec![35, 46], ],
            vec![ vec![0, 1, 2, 4], vec![6, 7, 8, 9], vec![11, 12, 13, 14], vec![17, 21, 22, 23, 24], vec![26, 27, 28, 29, 30], vec![32, 33, 34], vec![36, 37, 38, 40, 41], vec![47, 48, 49, 50], ],
        ];
        check_btree_correctness(&map, expected_keys_6);
        println!("Algorithm test done!");
    }


    #[test]
    fn iter_tests() {
        let mut map = BTreeMap::<i32, String>::new();

        for j in 0..B * 2 {
            for i in 0..10 {
                map.insert((i * (B * 2 - 1) + j) as i32, (i * (B * 2 - 1) + j + 1).to_string());
            }
        }

        let mut size = 0;
        let mut prev_k = None;
        for (k, v) in map.iter() {
            assert!(v == &(&(k + 1)).to_string());
            if prev_k.is_none() {
                prev_k = Some(k);
            } else {
                assert_eq!(*prev_k.unwrap(), k - 1);
                prev_k = Some(k);
            }
            size += 1;
        }

        assert_eq!(size, 51);
    }
}
