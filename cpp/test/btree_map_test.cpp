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
// Test cases for the B-Tree Map

#include "btree_map.h"
#include <cassert>  // for assert
#include <iostream>
#include <string>

static const size_t B_FACTOR = 3;

template <std::size_t B>
static void display(btree_map::BTreeMap<int, std::string, B> const& map) {
  std::vector<std::vector<btree_map::TreeNode<int, std::string>>> result;
  map.bfs(result);
  for (auto i = 0; i < result.size(); i++) {
    std::cout << "At layer " << i << " of the B-Tree map:" << std::endl;
    for (auto j = 0; j < result[i].size(); j++) {
      std::cout << "{";
      for (auto k = 0; k < result[i][j].size() - 1; k++) {
        std::cout << *result[i][j][k].first << ", ";
      }
      std::cout << *result[i][j][result[i][j].size() - 1].first << "}, ";
    }
    std::cout << std::endl;
    std::cout << std::endl;
  }

  std::cout << "Preorder keys: ";
  std::vector<btree_map::Element<int, std::string>> preorder;
  map.preorder(preorder);
  for (auto i = 0; i < preorder.size(); i++) {
    std::cout << *preorder[i].first << ", ";
  }
  std::cout << std::endl;
}

static void check_btree_correctness(
    btree_map::BTreeMap<int, std::string, B_FACTOR> const& map,
    std::vector<std::vector<std::vector<int>>> const& expected_keys) {
  size_t total_elements = 0;
  for (auto i = 0; i < expected_keys.size(); i++) {
    for (auto j = 0; j < expected_keys[i].size(); j++) {
      total_elements += expected_keys[i][j].size();
      for (auto k = 0; k < expected_keys[i][j].size(); k++) {
        auto v = map.find(expected_keys[i][j][k]);
        assert(v != std::nullopt &&
               *(v->get()) == std::to_string(expected_keys[i][j][k] + 1));
      }
    }
  }

  std::vector<std::vector<btree_map::TreeNode<int, std::string>>> result;
  map.bfs(result);
  assert(result.size() == expected_keys.size());
  for (auto i = 0; i < result.size(); i++) {
    assert(result[i].size() == expected_keys[i].size());
    for (auto j = 0; j < result[i].size(); j++) {
      assert(result[i][j].size() == expected_keys[i][j].size());
      for (auto k = 0; k < result[i][j].size(); k++) {
        assert(*result[i][j][k].first == expected_keys[i][j][k]);
      }
    }
  }
  std::vector<btree_map::Element<int, std::string>> preorder;
  map.preorder(preorder);
  assert(preorder.size() == total_elements);
  for (auto i = 0; i < preorder.size() - 1; i++) {
    assert(*preorder[i].first < *preorder[i + 1].first);
  }
}

static void algorithm_coverage_tests() {
  auto map = btree_map::BTreeMap<int, std::string, B_FACTOR>{};

  for (auto j = 0; j < B_FACTOR * 2; j++) {
    for (auto i = 0; i < 10; i++) {
      map.insert(i * (B_FACTOR * 2 - 1) + j,
                 std::to_string(i * (B_FACTOR * 2 - 1) + j + 1));
    }
  }

  // clang-format off
  const std::vector<std::vector<std::vector<int>>> expected_keys = {
      { {15, 31}, },
      { {2, 5, 10}, {18, 21, 25}, {35, 40, 43, 46}, },
      { {0, 1}, {3, 4}, {6, 7, 8, 9}, {11, 12, 13, 14}, {16, 17}, {19, 20}, {22, 23, 24}, {26, 27, 28, 29, 30}, {32, 33, 34}, {36, 37, 38, 39}, {41, 42}, {44, 45}, {47, 48, 49, 50}, },
  };
  check_btree_correctness(map, expected_keys);

  // Erase key '44' will cause its node to merge with its left sibling
  auto v = map.erase(44);
  assert(v != std::nullopt && *(v->get()) == std::to_string(44 + 1));
  const std::vector<std::vector<std::vector<int>>> expected_keys_1 = {
      { {15, 31}, },
      { {2, 5, 10}, {18, 21, 25}, {35, 40, 46}, },
      { {0, 1}, {3, 4}, {6, 7, 8, 9}, {11, 12, 13, 14}, {16, 17}, {19, 20}, {22, 23, 24}, {26, 27, 28, 29, 30}, {32, 33, 34}, {36, 37, 38, 39}, {41, 42, 43, 45}, {47, 48, 49, 50}, },
  };
  check_btree_correctness(map, expected_keys_1);

  // Erase key '19' will cause its node to merge with its left sibling
  v = map.erase(19);
  assert(v != std::nullopt && *(v->get()) == std::to_string(19 + 1));
  const std::vector<std::vector<std::vector<int>>> expected_keys_2 = {
      { {15, 31}, },
      { {2, 5, 10}, {21, 25}, {35, 40, 46}, },
      { {0, 1}, {3, 4}, {6, 7, 8, 9}, {11, 12, 13, 14}, {16, 17, 18, 20}, {22, 23, 24}, {26, 27, 28, 29, 30}, {32, 33, 34}, {36, 37, 38, 39}, {41, 42, 43, 45}, {47, 48, 49, 50}, },
  };
  check_btree_correctness(map, expected_keys_2);

  map.erase(42);
  map.erase(43);

  // Erase key '45' now will cause its node to borrow one element from its left
  // sibling
  v = map.erase(45);
  assert(v != std::nullopt && *(v->get()) == std::to_string(45 + 1));
  const std::vector<std::vector<std::vector<int>>> expected_keys_3 = {
      { {15, 31}, },
      { {2, 5, 10}, {21, 25}, {35, 39, 46}, },
      { {0, 1}, {3, 4}, {6, 7, 8, 9}, {11, 12, 13, 14}, {16, 17, 18, 20}, {22, 23, 24}, {26, 27, 28, 29, 30}, {32, 33, 34}, {36, 37, 38}, {40, 41}, {47, 48, 49, 50}, },
  };
  check_btree_correctness(map, expected_keys_3);

  map.erase(18);
  map.erase(20);

  // Erase key '16' now will cause its node to merge to its right sibling, then
  // trigger its parent node to merge to its left sibling
  v = map.erase(16);
  assert(v != std::nullopt && *(v->get()) == std::to_string(16 + 1));
  const std::vector<std::vector<std::vector<int>>> expected_keys_4 = {
      { {31}, },
      { {2, 5, 10, 15, 25}, {35, 39, 46}, },
      { {0, 1}, {3, 4}, {6, 7, 8, 9}, {11, 12, 13, 14}, {17, 21, 22, 23, 24}, {26, 27, 28, 29, 30}, {32, 33, 34}, {36, 37, 38}, {40, 41}, {47, 48, 49, 50}, },
  };
  check_btree_correctness(map, expected_keys_4);

  // Erase key '39' now will cause it to borrow element 40 from its child node,
  // then in turn it triggers this child node to merge to its left sibling.
  v = map.erase(39);
  assert(v != std::nullopt && *(v->get()) == std::to_string(39 + 1));
  const std::vector<std::vector<std::vector<int>>> expected_keys_5 = {
      { {31}, },
      { {2, 5, 10, 15, 25}, {35, 46}, },
      { {0, 1}, {3, 4}, {6, 7, 8, 9}, {11, 12, 13, 14}, {17, 21, 22, 23, 24}, {26, 27, 28, 29, 30}, {32, 33, 34}, {36, 37, 38, 40, 41}, {47, 48, 49, 50}, },
  };
  check_btree_correctness(map, expected_keys_5);

  // Erase key '0' now will cause its node to merge to its left sibling
  v = map.erase(3);
  assert(v != std::nullopt && *(v->get()) == std::to_string(3 + 1));
  const std::vector<std::vector<std::vector<int>>> expected_keys_6 = {
      { {31}, },
      { {5, 10, 15, 25}, {35, 46}, },
      { {0, 1, 2, 4}, {6, 7, 8, 9}, {11, 12, 13, 14}, {17, 21, 22, 23, 24}, {26, 27, 28, 29, 30}, {32, 33, 34}, {36, 37, 38, 40, 41}, {47, 48, 49, 50}, },
  };
  // clang-format on
  check_btree_correctness(map, expected_keys_6);

  for (auto i = 0; i < 51; i++) {
    map.erase(i);
    std::cout << "After erase " << i << std::endl;
    display<B_FACTOR>(map);
  }
  std::cout << "Algorithm test done!" << std::endl;
}

static void check_btree_sanity(
    btree_map::BTreeMap<int, std::string, B_FACTOR> const& map) {
  std::vector<btree_map::Element<int, std::string>> preorder;
  map.preorder(preorder);
  for (auto i = 0; i < preorder.size() - 1 && preorder.size() != 0; i++) {
    assert(*preorder[i].first < *preorder[i + 1].first);
  }
}

static int my_pow(size_t x, unsigned int p) {
    if (p == 0) return 1;
    if (p == 1) return x;

    int tmp = my_pow(x, p/2);
    if (p % 2 == 0) {
        return tmp * tmp;
    }
    else {
        return x * tmp * tmp;
    }
}

static void stress_tests() {
  // Max capacity for a 3 layer B-Tree with B factor set to 32 is 262,143
  size_t max_elements = 0;
  for (auto i = 0; i < 7; i++) {
      max_elements += my_pow(2 * B_FACTOR, i) * (2 * B_FACTOR + 1);
  }

  std::cout << "stress_tests max_elements " << max_elements << std::endl;
  auto map = btree_map::BTreeMap<int, std::string, B_FACTOR>{};

  size_t total_elements = 0;
  // Try fill the tree, in a pseudo random manner
  while (total_elements < max_elements / 40) {
    auto key = rand() % max_elements;
    if (std::nullopt == map.find(key)) {
      map.insert(key, std::to_string(key + 1));
      total_elements++;
      check_btree_sanity(map);
      if (key % 4 == 0) {  // Mix insert with erase
        auto erase = rand() % max_elements;
        if (std::nullopt != map.find(erase)) {
          auto v = map.erase(erase);
          assert(v != std::nullopt && *(v->get()) == std::to_string(erase + 1));
          check_btree_sanity(map);
          total_elements--;
        }
      }
    }
  }
  display<B_FACTOR>(map);
  check_btree_sanity(map);

  // Try delete all element, in a pseudo random manner
  std::vector<btree_map::Element<int, std::string>> preorder;
  map.preorder(preorder);
  while (preorder.size() != 0) {
    auto i = rand() % preorder.size();
    auto k = *preorder[i].first;
    preorder.erase(preorder.begin() + i);
    auto e = map.find(k);
    assert(e != std::nullopt && *(e->get()) == std::to_string(k + 1));
    auto v = map.erase(k);
    check_btree_sanity(map);
    assert(v != std::nullopt && *(v->get()) == std::to_string(k + 1));
    total_elements--;
  }

  map.preorder(preorder);
  assert(preorder.size() == 0);
  assert(total_elements == 0);
  std::cout << "Stress test done!" << std::endl;
}

int main(int argc, char** argv) {
  algorithm_coverage_tests();

  stress_tests();

  return 0;
}
// clang++ -g --std=c++17 -fsanitize=address -fno-omit-frame-pointer
// btree_map_test.cpp
// clang-tidy btree_map_test.cpp -extra-arg=-std=c++17
