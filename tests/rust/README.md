VeriFast for Rust test cases and examples
=========================================

Subdirectories:
- `unverified`: contains some library crates used by the verified examples, but which have not been verified themselves. However, a specification for their API is available in their `spec` subdirectories.
- `purely_unsafe`: some purely unsafe examples that have been verified using VeriFast to have no undefined behavior.
- `safe_abstraction`: some examples of crates offering functions that are verified using VeriFast to be safe for use by typechecked code but that use `unsafe` code internally. This functionality is based on the ideas of the [RustBelt](https://plv.mpi-sws.org/rustbelt/) project.

Open an example in the VeriFast IDE (`bin/vfide`) to verify it. After verifying a program, you can inspect a function's symbolic execution tree by choosing Show execution tree and selecting the function in the drop-down menu in the upper right corner of the VeriFast window. Click any node in the tree to step through the symbolic execution path leading up to that node and inspect the symbolic heap, symbolic store (local variable bindings), and path condition at each step in a debugger-like experience.

To verify all examples using the command-line tool, run `mysh testsuite.mysh`.

Disclaimer:
- We aim for VeriFast to be sound (i.e. to report "0 errors found" only if no execution of the input program has undefined behavior and safe functions comply with their type's interpretation as defined by RustBelt); however, in contrast to some other tools such as [RefinedRust](https://plv.mpi-sws.org/refinedrust/), VeriFast itself has not been formally verified, so unknown bugs are almost certainly present in the tool that may cause the tool to report "0 errors found" incorrectly in some cases. There may also be known unsoundnesses; these should all be recorded either here or as [issues](https://github.com/verifast/verifast/issues?q=is%3Aissue+is%3Aopen+label%3Aunsoundness) with label `unsoundness`.
- One known unsoundness is that VeriFast currently does not take into account [all of the sources of undefined behavior](https://doc.rust-lang.org/reference/behavior-considered-undefined.html). For now, VeriFast does (absent bugs) verify absence of data races, out-of-bounds pointer arithmetic, and accesses of dangling places, but it currently does not verify compliance with Rust's alignment requirements or its [aliasing restrictions](https://perso.crans.org/vanille/treebor/), or its rules on producing invalid values.