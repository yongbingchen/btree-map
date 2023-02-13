# B-Tree Map

A Rust and C++ implementation of B-Tree Map, the C++ version is created mainly for algorithm verification purpose.

Get the full document with command "cargo doc", run the sample application with command "cargo run", run the tests with command "cargo test", or "cargo test --features stress_test" to run the stress test.

It implements a subset, but complete interface of standard B-Tree Map structure, includes:

 - get
 - get_mut
 - insert
 - remove
 - iter
 - iter_mut

The B factor is defined as a const in src/lib/btree_node.rs, it cannot be a generic parameter due to current Rust feature limitation, revise it manually to suit your use case.
