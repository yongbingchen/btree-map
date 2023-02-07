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
// Sample application for the B-Tree Map library

#include "btree_map.h"
#include <iostream>
#include <string>

static const size_t B_FACTOR = 2;
int main(int argc, char** argv) {
  auto movie_reviews =
      btree_map::BTreeMap<std::string, std::string, B_FACTOR>{};

  // Review some movies.
  movie_reviews.insert("Office Space",
                       "Deals with real issues in the workplace.");
  movie_reviews.insert("Pulp Fiction", "Masterpiece.");
  movie_reviews.insert("The Godfather", "Very enjoyable.");
  movie_reviews.insert("The Blues Brothers", "Eye lyked it a lot.");

  // Check for a specific one.
  if (std::nullopt == movie_reviews.find("Les Misérables")) {
    std::cout << "We've got some reviews, but Les Misérables ain't one."
              << std::endl;
  }

  // Oops, this review has a lot of spelling mistakes, let's delete it.
  movie_reviews.erase("The Blues Brothers");

  // Look up the values associated with some keys.
  std::vector<std::string> to_find = {"Up!", "Office Space"};
  for (auto const& movie : to_find) {
    auto review = movie_reviews.find(movie);
    if (review != std::nullopt) {
      std::cout << "Movie " << movie << " has review: " << *review->get()
                << std::endl;
    } else {
      std::cout << "Movie " << movie << " does not have review." << std::endl;
    }
  }
  return 0;
}
