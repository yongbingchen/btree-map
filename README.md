# B-Tree Map

A Rust and C++ implementation of B-Tree Map, the C++ version is created mainly for algorithm verification purpose.

Get the full document with command "cargo doc", run the sample application with command "cargo run".

It's about 5% slower than current std implementation, use command "cargo test --features stress_test -- --nocapture" to run the benchmark and stress test.

It implements a subset, but complete interfaces of the standard B-Tree Map structure, including:

 - get
 - get_mut
 - insert
 - remove
 - iter
 - iter_mut

The B factor is defined as a const in src/lib/btree_node.rs, it cannot be a generic parameter due to current Rust feature limitation, revise it manually if needed.
