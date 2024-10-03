VeriFast for Rust purely unsafe test cases and examples
=======================================================

To play with an example, open it in the VeriFast IDE (`bin/vfide`).

- `httpd.rs`, `httpd_vec.rs`, and `httpd_mt.rs` implement a tiny HTTP daemon that listens on port 10000, appends each request to a buffer, and responds to each request with the contents of this buffer. They use the unverified `platform` crate at `../unverified/platform` to access the operating system's sockets and multithreading APIs. To build them, type

      rustc --extern platform=../unverified/platform/target/debug/libplatform.rlib -L dependency=../unverified/platform/target/debug/deps httpd.rs

- `tree.rs`, `tree2.rs`, and `tree3.rs` are variations of a function that marks a tree in constant space, by rotating the nodes on the path from the root to the current node
- `deque.rs` implements a doubly-linked list