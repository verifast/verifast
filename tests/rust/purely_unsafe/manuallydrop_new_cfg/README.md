# ManuallyDrop::new CFG regression

`forget.rs` must verify: the identity lowering of `ManuallyDrop::new` has no unwind edge.
`shared_cleanup.rs` checks that real unwind paths of other calls are kept. The `should_fail`
cases check that normal and unwind postconditions are still verified, and `dead_code_pre.rs`
that a contradictory precondition is still reported (`dead_code_pre.sh` runs it under `sh` so the
exit status can be checked on Windows too). `shared_false_unwind.rs` takes the normal branch first, so
the expected unwind error is reached after the normal path has been checked.
