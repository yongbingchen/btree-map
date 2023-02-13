// Copyright 2023 Yongbing Chen
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions: The above copyright
// notice and this permission notice shall be included in all copies or
// substantial portions of the Software. THE SOFTWARE IS PROVIDED "AS IS",
// WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED
// TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
// NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE
// FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
// TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR
// THE USE OR OTHER DEALINGS IN THE SOFTWARE.
//
// A C++ implementation of B-Tree Map, from
// http://opendatastructures.org/ods-cpp/14_2_B_Trees.html#38721
// The book and accompanying source code are free (libre and gratis) and are
// released under a Creative Commons Attribution License. Users are free to
// copy, distribute, use, and adapt the text and source code, even commercially.
//
// B-Tree algorithm can be visualized with tool from
// https://people.ksp.sk/~kuko/gnarley-trees/Btree.html
//
// clang-format off
// insert(key, value):
// 	Recursive from root node, try find 'key' at current/parent node.
// 	If node's keys[i] is the smallest keys[i] > key, go down to children[i] to keep searching.
// 		If the children[i] found is a leaf node, then:
// 			1. Insert (key, value) into to this children[i] node
// 			2. After insertion, if children[i].size() == 2B, then split this children[i] node:
// 				1. Create a new node, move keys[0..B - 1] to the new node.
// 				2. Move keys[B..2B - 1] ahead to keys[0..B - 1] in original node.
// 				3. Return the new node from this split operation.
// 			3. And if split(children[i]) returns a new node:
// 				1. Promote the greatest element at this new node (at keys[B -1]) to its parent.
// 				           And the original children[i..2B] will be move back one slot to children[i + 1..2B + 1].
// 				2. Add this new node to its parent (as its new children[i])
// 				3. Recursive back to next higher level, handle parent add one element event (does it need split too?).
//
// erase(key):
// 	Recursive from root node, try find 'key' at current/parent node.
// 	If keys[i] is the smallest keys[i] > key, go down to children[i] to keep searching.
// 		If found 'key' at node children[i], and it's a leaf node, remove it.
// 		Then handle_element_removal(Node &parent, size_t child_idx):
// 			After remove an element, if children[child_idx].size < B, then try to re-balance the B-Tree:
// 			1. If its left sibling node children[child_idx - 1] exist, merge node children[child_idx] with node children[child_idx - 1] (now the merged node size is less than 2B):
// 			    merge(parent, child_idx - 1, children[child_idx - 1], children[child_idx]);
// 			2. Else if its right sibling node children[child_idx + 1] exist, merge node children[child_idx] with children[child_idx + 1]:
// 			    merge(parent, child_idx, children[child_idx], children[child_idx + 1]);
// 			3. Else if its right sibling children[child_idx + 1].size() > B (also must be another leaf node, from B-Tree definition), try borrow one element from it:
// 				1. Remove the smallest, the first element from children[child_idx + 1].
// 				2. Replace element at keys[child_idx] with this smallest element from children[child_idx + 1].
// 				3. Add the replaced parent element at keys[child_idx] to the end of node children[child_idx]. Stop here.
// 			4. Else if its left sibling children[child_idx - 1].size() > B, try borrow one element from it:
// 				1. Remove the largest, the last element from children[child_idx - 1].
// 				2. Replace parent element at keys[child_idx - 1] with this element from children[child_idx - 1].
// 				3. Add the replaced element from keys[child_idx - 1] to the front of node children[child_idx]. Stop here.
// 		If found the key at a non-leaf node, at keys[i], remove it.
// 		After remove it, need to borrow one element from its children to keep the tree structure:
// 		Try borrow one element from this keys[i]'s successor in preorder, which is the last element of node at children[i]
// 			1. Remove the last element of node at children[i], insert at keys[i] of current node.
// 			2. Recursive do this operation utill children[i] is a leaf node.
// 			2. Remove an element from children[i], then it turns to same routine as above.
// 		Borrow will not trigger merge, so it's not recursive.
// 		One Merge operation invovles three nodes: two siblings, and their parent.
// 		Merge cause parent node to lose one element, so need recursive to next level to handle it
//
// merge(parent, merge_to_idx, left_child, right_child):
// 	1. Remove the element from parent node at index of the key[merge_to_idx], insert to left_child.
// 	2. Merge node right_child to node left_child, then delete right_child.
// 	3. Let parents->children[merge_to_idx] point to the merged child, the left_child.
// 	4. Handle the removal of the element at parent node key[merge_to_idx]:
// 	    1. Move forward one slot for all pointers, children[merge_to_idx + 1]..children[2B] to children[merge_to_idx]..children[2B - 1].
// 	    2. If the parent.size() == 0 after removal, replace it's content with the merged children[merge_to_idx], and delete the children[merge_to_idx].
// 	    3. The recursive go back another level to erase, to handle the parent node lost one element event.
//
// clang-format on

#include <functional>  // For std::less and std::greater
#include <memory>
#include <optional>
#include <vector>

#pragma once
namespace btree_map {

template <class K>
struct DefaultCompare {
  int operator()(const K& lhs, const K& rhs) {
    if (std::greater<K>{}(lhs, rhs)) {
      return 1;
    } else if (std::less<K>{}(lhs, rhs)) {
      return -1;
    }
    return 0;
  }
};

template <class K, class V>
using Element = std::pair<std::unique_ptr<K>, std::unique_ptr<V>>;

template <class K, class V>
using TreeNode = std::vector<Element<K, V>>;

namespace btree_map_private {
template <class K, class V, std::size_t B, class Compare = DefaultCompare<K>,
          class KAllocator = std::allocator<K>,
          class VAllocator = std::allocator<V>>
// requires Compare<K>;
struct Node {
  // Maximum number of elements is 2B - 1, the last slot is for internal usage.
  // Using pointers for key/value breaks the basic principle/benefit of using a
  // B-tree. This implementation is just for algorithm practice purpose, see
  // https://stackoverflow.com/questions/16379359/b-tree-with-variable-length-keys
  std::unique_ptr<K> keys[2 * B];
  std::unique_ptr<V> values[2 * B];
  // Maximum number of children is 2B, the last slot is for internal usage.
  std::unique_ptr<Node> children[2 * B + 1];

  // Insert operation allows to increase node's total elements to 2B: will then
  // follow with a split
  void insert(std::unique_ptr<K> k, std::unique_ptr<V> v) {
    for (auto i = 0; i < 2 * B; i++) {
      if (keys[i].get() != nullptr && Compare{}(*k, *keys[i]) > 0) {
        continue;
      }
      for (auto j = 2 * B - 1; j > i; j--) {
        keys[j] = std::move(keys[j - 1]);
        values[j] = std::move(values[j - 1]);
      }
      keys[i] = std::move(k);
      values[i] = std::move(v);
      break;
    }
  }

  // Add a child node at index position
  void add_child(std::unique_ptr<Node> child, const size_t index) {
    for (auto i = 2 * B; i > index; i--) {
      children[i] = std::move(children[i - 1]);
    }
    children[index] = std::move(child);
  }

  std::unique_ptr<Node> remove_child(const size_t index) {
      auto ret = std::move(children[index]);
      for (auto i = index; i < 2 * B; i++) {
          children[i] = std::move(children[i + 1]);
      }
      return ret;
  }

  // Remove the element at index, return the key/value pair of this element
  Element<K, V> remove(const size_t index) {
    Element<K, V> e{std::move(keys[index]), std::move(values[index])};

    for (auto i = index; i < 2 * B - 1 && keys[i + 1].get() != nullptr; i++) {
      keys[i] = std::move(keys[i + 1]);
      values[i] = std::move(values[i + 1]);
    }
    return e;
  }

  // Split a node to two, if its elements number is 2B
  // After split, the new node will hold first B elements, and the remaining B
  // elements will be in the original node. The new node will be returned after
  // split.
  std::unique_ptr<Node> split() {
    if (keys[2 * B - 1].get() == nullptr) {
      return nullptr;
    }

    auto new_child = std::make_unique<Node>();
    for (auto i = 0; i < B; i++) {
      new_child->keys[i] = std::move(keys[i]);
      new_child->values[i] = std::move(values[i]);
      new_child->children[i] = std::move(children[i]);
    }
    // Last element of a non-leaf node is allowed to have empty right child
    new_child->children[B] = nullptr;

    for (auto i = 0; i < B; i++) {
      keys[i] = std::move(keys[i + B]);
      values[i] = std::move(values[i + B]);
      children[i] = std::move(children[i + B]);
    }
    children[B] = std::move(children[2 * B]);
    return new_child;
  }

  bool is_leaf() const { return children[0].get() == nullptr; }
  size_t size() const {
    for (auto i = 2 * B; i > 0; i--) {
      if (keys[i - 1] != nullptr) {
        return i;
      }
    }
    return 0;
  }

  // Breadth first traverse, to show the actual structure of the tree
  void bfs(int const layer,
           std::vector<std::vector<TreeNode<K, V>>>& result) const {
    if (keys[0].get() == nullptr) {
      return;
    }

    std::vector<Element<K, V>> node;
    for (auto i = 0; i < 2 * B - 1; i++) {
      if (keys[i].get() == nullptr) {
        break;
      }
      node.push_back(std::make_pair(std::make_unique<K>(*keys[i]),
                                    std::make_unique<V>(*values[i])));
    }

    if (result.size() > layer) {
      result[layer].push_back(std::move(node));
    } else {
      std::vector<TreeNode<K, V>> l;
      l.push_back(std::move(node));
      result.push_back(std::move(l));
    }

    for (auto i = 0; i < 2 * B; i++) {
      if (children[i].get() == nullptr) {
        break;
      }
      children[i]->bfs(layer + 1, result);
    }
  }

  // Preorder traverse to get the ordered result
  void preorder(std::vector<Element<K, V>>& result) const {
    for (auto i = 0; i < 2 * B; i++) {
      if (children[i].get() != nullptr) {
        children[i]->preorder(result);
      }
      if (keys[i].get() != nullptr) {
        result.push_back(std::make_pair(std::make_unique<K>(*keys[i]),
                                        std::make_unique<V>(*values[i])));
      }
    }
  }

  // std::weak_ptr<struct Node> parent; //B-tree does not store pointers to
  // their parents by definition.
};
}  // namespace btree_map_private

template <class K, class V, std::size_t B, class Compare = DefaultCompare<K>,
          class KAllocator = std::allocator<K>,
          class VAllocator = std::allocator<V>>
class BTreeMap {
 public:
  // BTreeMap APIs are not thread-safe.
  bool insert(const K& key, const V& value) {
    auto k = std::make_unique<K>(key);
    auto v = std::make_unique<V>(value);
    auto w = add_recursive(std::move(k), std::move(v), root);
    if (w.get() == nullptr) {
      return false;
    }
    // Root was split, w is the new node split from original root, which holds
    // the "smaller" half of the updated root node before split
    auto new_root = std::make_unique<btree_map_private::Node<K, V, B>>();
    // Promote the largest element of the "smaller" half as the new root node's
    // only element
    auto x = w->remove(B - 1);
    new_root->keys[0] = std::move(x.first);
    new_root->values[0] = std::move(x.second);
    new_root->children[0] = std::move(w);
    new_root->children[1] = std::move(root);
    root = std::move(new_root);
    return true;
  }

  std::optional<std::unique_ptr<V>> erase(const K& key) {
    auto k = std::make_unique<K>(key);
    auto ret = erase_recursive(k, root);
    // If the root is empty after erase, use its first (and should be the only)
    // child as new root
    if (root->size() == 0 && root->children[0].get() != nullptr) {
      root = std::move(root->children[0]);
    }
    return ret;
  }

  std::optional<std::unique_ptr<V>> find(const K& key) const {
    auto k = std::make_unique<K>(key);
    return find_recursive(k, root);
  }

  void bfs(std::vector<std::vector<TreeNode<K, V>>>& result) const {
    root->bfs(0, result);
  }
  void preorder(std::vector<Element<K, V>>& result) const {
    root->preorder(result);
  }
  BTreeMap() : root(std::make_unique<btree_map_private::Node<K, V, B>>()) {}

 private:
  // Find key x at the ordered, null-padded array keys[].
  // If found x at keys[m], then return -(m + 1);
  // Otherwise, return the smallest index lo, in which keys[lo] > x, so
  // children[lo] will point to the next search node or children[lo] == nullptr,
  // which means the child node does not exist yet, thus the end of the
  // recursive search;
  int find_it(const std::unique_ptr<K> keys[], const size_t length,
              std::unique_ptr<K> const& k) const {
    size_t lo = 0, hi = length;
    while (hi != lo) {
      size_t m = (hi + lo) / 2;
      int cmp = keys[m].get() == nullptr ? -1 : Compare{}(*k, *keys[m]);
      if (cmp < 0) {
        hi = m;  // Look in first half
      } else if (cmp > 0) {
        lo = m + 1;  // Look in second half
      } else {
        return -(m + 1);  // Found it
      }
    }
    return lo;
  }

  std::optional<std::unique_ptr<V>> find_recursive(
      std::unique_ptr<K> const& k,
      std::unique_ptr<btree_map_private::Node<K, V, B>> const& u) const {
    int i = find_it(u->keys, 2 * B - 1, k);
    if (i < 0) {
      return std::make_unique<V>(*u->values[-(i + 1)]);
    }
    if (u->children[i].get() == nullptr) {
      return {};
    } else {
      return find_recursive(k, u->children[i]);
    }
  }

  std::unique_ptr<btree_map_private::Node<K, V, B>> add_recursive(
      std::unique_ptr<K> k, std::unique_ptr<V> v,
      std::unique_ptr<btree_map_private::Node<K, V, B>>& u) {
    int i = find_it(u->keys, 2 * B - 1, k);
    if (i < 0) {
      // Key exists, no operation
      // TODO: return existing value at this situation
      return nullptr;
    }
    if (u->children[i].get() == nullptr) {
      // No left child at insert position, by definition this is a leaf node,
      // just insert it to this node, then maybe split it later
      u->insert(std::move(k), std::move(v));
    } else {
      auto w = add_recursive(std::move(k), std::move(v), u->children[i]);
      if (w != nullptr) {
        // Child was split, w is the new child node (the original child is still
        // valid). Promote the largest element in the new child (the smaller
        // group) to its parent, to makes a slot in its parent to hold this new
        // child
        auto x = w->remove(B - 1);
        u->insert(std::move(x.first), std::move(x.second));
        u->add_child(std::move(w), i);
      }
    }
    return u->split();
  }

  Element<K, V> remove_smallest(
      std::unique_ptr<btree_map_private::Node<K, V, B>>& u) {
    if (u->is_leaf()) {
      return u->remove(0);
    }

    auto e = remove_smallest(u->children[0]);
    check_child_underflow(u, u->children[0], 0);
    return e;
  }

  std::optional<std::unique_ptr<V>> erase_recursive(
      std::unique_ptr<K>& k,
      std::unique_ptr<btree_map_private::Node<K, V, B>>& u) {
    std::optional<std::unique_ptr<V>> ret;
    int i = find_it(u->keys, 2 * B - 1, k);
    if (i < 0) {  // Found key at this node
      i = -(i + 1);
      auto e = u->remove(i);
      ret = std::move(e.second);
      if (!u->is_leaf()) {
        // Borrow one from its child to keep the tree structure
        auto borrow = remove_smallest(u->children[i + 1]);
        u->insert(std::move(borrow.first), std::move(borrow.second));
        check_child_underflow(u, u->children[i + 1], i + 1);
      }
      return ret;
    } else if (u->children[i].get() != nullptr) {
      ret = erase_recursive(k, u->children[i]);
      if (ret != std::nullopt) {
        check_child_underflow(u, u->children[i], i);
        return ret;
      }
    }

    return {};
  }

  // Whenever an element is removed from a child, need to check if it's
  // underflow, and perform tree re-balance if needed.
  void check_child_underflow(
      std::unique_ptr<btree_map_private::Node<K, V, B>>& parent,
      std::unique_ptr<btree_map_private::Node<K, V, B>>& child,
      const size_t child_idx) {
    if (child == nullptr) {
      return;
    }

    if (child->size() < B - 1) {  // Child node underflow
      auto has_left_sibling = child_idx != 0;
      auto has_right_sibling =
          child_idx < 2 * B && parent->children[child_idx + 1].get() != nullptr;
      if (has_left_sibling && parent->children[child_idx - 1]->size() <= B) {
        merge(parent, child_idx - 1, parent->children[child_idx - 1], child);
      } else if (has_right_sibling &&
                 parent->children[child_idx + 1]->size() <= B) {
        merge(parent, child_idx, child, parent->children[child_idx + 1]);
      } else if (has_left_sibling) {
        borrow_from_left(parent, child_idx, child,
                         parent->children[child_idx - 1]);
      } else if (has_right_sibling) {
        borrow_from_right(parent, child_idx, child,
                          parent->children[child_idx + 1]);
      }
    }
  }

  void borrow_from_right(
      std::unique_ptr<btree_map_private::Node<K, V, B>>& parent,
      const size_t child_idx,
      std::unique_ptr<btree_map_private::Node<K, V, B>>& child,
      std::unique_ptr<btree_map_private::Node<K, V, B>>& right_sibling) {
    auto e = right_sibling->remove(0);
    auto p = parent->remove(child_idx);
    parent->insert(std::move(e.first), std::move(e.second));
    child->insert(std::move(p.first), std::move(p.second));
    // Move the first child of right_sibling as the last child of left node
    auto r_child = right_sibling->remove_child(0);
    auto last = child->size();
    child->add_child(std::move(r_child), last);
  }

  void borrow_from_left(
      std::unique_ptr<btree_map_private::Node<K, V, B>>& parent,
      const size_t child_idx,
      std::unique_ptr<btree_map_private::Node<K, V, B>>& child,
      std::unique_ptr<btree_map_private::Node<K, V, B>>& left_sibling) {
    auto last = left_sibling->size() - 1;
    auto e = left_sibling->remove(last);
    auto p = parent->remove(child_idx - 1);
    parent->insert(std::move(e.first), std::move(e.second));
    child->insert(std::move(p.first), std::move(p.second));
    // Move the last child of left_sibling as the first child of the right node
    auto l_child = left_sibling->remove_child(last + 1);
    child->add_child(std::move(l_child), 0);
  }

  // Merge right_child to its left sibling, and let parent->children[child_idx]
  // point to the merged node
  void merge(std::unique_ptr<btree_map_private::Node<K, V, B>>& parent,
             const size_t merge_to_idx,
             std::unique_ptr<btree_map_private::Node<K, V, B>>& left_child,
             std::unique_ptr<btree_map_private::Node<K, V, B>>& right_child) {
    // Merge cause parent to lose one child, remove one element to make room for
    // it.
    auto e = parent->remove(merge_to_idx);
    left_child->insert(std::move(e.first), std::move(e.second));
    auto right_child_size = right_child->size();
    for (size_t i = left_child->size(), j = 0; j < right_child_size; i++, j++) {
      left_child->keys[i] = std::move(right_child->keys[j]);
      left_child->values[i] = std::move(right_child->values[j]);
      left_child->children[i] = std::move(right_child->children[j]);
    }
    left_child->children[left_child->size()] =
        std::move(right_child->children[right_child_size]);

    // Move all other right children ahead one slot, implictly release the
    // right_child node.
    for (auto i = merge_to_idx + 1; i < 2 * B; i++) {
      parent->children[i] = std::move(parent->children[i + 1]);
    }
  }

  std::unique_ptr<btree_map_private::Node<K, V, B>> root;
};

}  // namespace btree_map
