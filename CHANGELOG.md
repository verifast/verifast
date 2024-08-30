# Changelog

## Unreleased

## 24.08.30 - 2024-08-30

Fixed a bug that caused the Rust test cases to fail on Windows if the `PATH` environment variable was spelled `Path` (as is the case typically, but not in our CI environment).

## 24.08 - 2024-08-27

### Breaking changes

We have made a number of breaking changes to make VeriFast sound with respect
to the fact that C compilers perform optimizations based on a view of C as a
high-level language, rather than as just a nicer syntax for assembly
language:

- VeriFast no longer allows reading uninitialized variables.
  - Commits:
    - https://github.com/verifast/verifast/commit/6a5c7b464e91578d24b6d82c6158670b90d62c8b
    - https://github.com/verifast/verifast/commit/7fa81165fa94fbd06e2873e05464300f5b6a85ab
    - https://github.com/verifast/verifast/commit/5917c642bcea07e7e50bc1ca68ad688924e10608
    - https://github.com/verifast/verifast/commit/c04e125e74e9db097babd7e69d4b419261c92fe7
    - https://github.com/verifast/verifast/commit/1beedcf96e7038702c6bebc61e6599ea27998956
  - Further reading on this aspect of C:
    - https://www.ralfj.de/blog/2019/07/14/uninit.html
    - https://godbolt.org/z/dYq1Gc9G4
    - https://htmlpreview.github.io/?https://github.com/C-memory-object-model-study-group/c-mom-sg/blob/master/notes/built_doc/cmom-0006-2021-03-08-clarifying-uninitialised-reads-v5.html
- VeriFast now treats a pointer as consisting of an address and a *provenance*.
  - Commits:
    - https://github.com/verifast/verifast/commit/bc170f8b539710386e4c855f4e5e29dc1d741388
    - https://github.com/verifast/verifast/commit/4d1efe1cf18083ab1c0ff54af0fb88a7336cef89
    - https://github.com/verifast/verifast/commit/6960d827e506b6eb55c8dfcf05747b7fedce8e4d
    - https://github.com/verifast/verifast/commit/c2f856e4c88af315448f7f28477b6e6465981e94
  - Command-line options `-assume_no_provenance` and `-assume_no_subobject_provenance` have
    been introduced to (partially) restore VeriFast's previous behavior.
  - Further reading on this aspect of C:
    - https://www.ralfj.de/blog/2018/07/24/pointers-and-bytes.html
    - https://godbolt.org/z/nj6bhMq4o
    - https://www.open-std.org/jtc1/sc22/wg14/www/docs/n3005.pdf
- VeriFast now verifies compliance with C's *effective types* rules.
  - Commits:
    - https://github.com/verifast/verifast/commit/aa47493326cd3c43ee5813b29a9615d129ec4734
    - https://github.com/verifast/verifast/commit/5c2987a856f9128e90a73177733e60430739e40a
    - https://github.com/verifast/verifast/commit/c2554e602e12b8fae8fc7c0e6fdf8c4a5ca246d3
    - https://github.com/verifast/verifast/commit/0771935ede8c3adc1f3f4aec210a8d88fa76d25a
    - https://github.com/verifast/verifast/commit/f8f060b2ac4dd2bb6556b334467f55fe8b3ce031
  - Command-line option `-fno-strict-aliasing` has been introduced to disable these checks.
  - Further reading on this aspect of C:
    - https://www.open-std.org/jtc1/sc22/wg21/docs/papers/2019/p1796r0.pdf
- VeriFast no longer allows arithmetic operations on signed integers to overflow, even when marked as `truncating`, unless the `-fwrapv` command-line option is specified.

See also the discussion at https://github.com/verifast/verifast/discussions/315 .

The VeriFast Tutorial has been updated.

### Other changes

Many minor bug fixes and improvements, including:
- Add support for `default` clauses in `switch` assertions and statements.
- VeriFast IDE: Add *Open Recent* menu.
- Add support for `continue` statements.
- Add support for partially applied generic predicate constructors.
- Add support for points-to chunks for bodyless structs.
- Add support for struct expressions (a.k.a. struct literals).
- Add basic support for multidimensional arrays.
- Add support in the VeriFast IDE and the VSCode extension to verify just
  the current function.
- Add lemma `div_rem_nonneg_unique` to `bin/prelude.h`.
- The VSCode extension now essentially has feature parity with the IDE
- Add the `-assume_left_to_right_evaluation` flag to allow postponing
  verification troubles that are due to C's unspecified evaluation order.
- Add support for `calloc`.
- Improved treatment of struct assignment.
- Add support for `stdarg.h`, i.e. implementing varargs functions.
- Add support for C11 `_Generic` expressions.

### Preview features

- *VeriFast for C++*: see the test cases at `tests/cxx`
- *VeriFast for Rust*: see the test cases at `tests/rust`
