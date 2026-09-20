This is the Rust standard library's [`alloc` crate](https://github.com/rust-lang/rust/tree/8925ea358a0f265ca61026aadc7ecc506c545cbe/library/alloc/src) (version `nightly-2026-08-21`),
minus the `linked_list`, `btree`, and `binary_heap` modules.

`boxed/iter.rs` additionally omits `BoxedArrayIntoIter` (and `boxed.rs` its
re-export), because VeriFast does not yet support structs with const parameters.
That omission applies to `original/` as well, so that the refinement checks keep
comparing like with like.
