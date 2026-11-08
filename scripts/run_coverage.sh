#!/usr/bin/env bash
set -euo pipefail

REPO_ROOT="/home/devin/verifast-src"
RAW_DIR="$REPO_ROOT/coverage/raw"
OUT_DIR="$REPO_ROOT/coverage"
REPORT_EXE="$REPO_ROOT/src/_build/default/coverage/vf_cov_report.exe"
UNIT_TEST_EXE="$REPO_ROOT/src/_build/default/unit_tests/unit_tests.exe"
JSON_TEST_EXE="$REPO_ROOT/src/_build/default/json_tests/json_tests.exe"

MODE="quick"
RUST_COV=false

show_help() {
  cat << 'HELP'
Usage: scripts/run_coverage.sh [OPTIONS]

Options:
  --quick       Run comprehensive fast suite: OCaml/Rust unit tests, C/C++/Java/Rust soundness suites,
                refinement-checker suite, VecDeque ring suite, Rocq check, Miri differential tests,
                mutation tests, and fuzzer (default)
  --full        Run full testsuite.mysh (~580 invocations) + unit tests + advanced suites
  --rust-cov    Enable Rust frontend coverage measurement using llvm-cov on vf_mir_exporter
  -h, --help    Show this help message
HELP
}

for arg in "$@"; do
  case "$arg" in
    --quick)
      MODE="quick"
      ;;
    --full)
      MODE="full"
      ;;
    --rust-cov)
      RUST_COV=true
      ;;
    -h|--help)
      show_help
      exit 0
      ;;
    *)
      echo "Unknown option: $arg"
      show_help
      exit 1
      ;;
  esac
done

export PATH="/home/devin/.cargo/bin:/tmp/vfdeps-adf88dc/bin:$REPO_ROOT/bin:$PATH"
export LD_LIBRARY_PATH="/tmp/vfdeps-adf88dc/lib:$REPO_ROOT/bin:${LD_LIBRARY_PATH:-}"
export PKG_CONFIG_PATH="/tmp/vfdeps-adf88dc/lib/pkgconfig:${PKG_CONFIG_PATH:-}"

echo "=== [1/4] Building Coverage Measurement & Unit Test Tools ==="
chmod -f u+w "$REPO_ROOT/bin/verifast" "$REPO_ROOT/bin/refinement-checker" 2>/dev/null || true
chmod -f u+w "$REPO_ROOT/bin/rustc-verifast" "$REPO_ROOT/bin/cargo-verifast" 2>/dev/null || true
"$REPO_ROOT/scripts/vf_lock_run.sh" make -C "$REPO_ROOT/src" verifast ../bin/refinement-checker ../bin/rustc-verifast ../bin/cargo-verifast
cp -f "$REPO_ROOT/src/_build/default/vfconsole/vfconsole.exe" "$REPO_ROOT/bin/verifast" 2>/dev/null || true
cp -f "$REPO_ROOT/src/_build/default/refinement_checker/main.exe" "$REPO_ROOT/bin/refinement-checker" 2>/dev/null || true
cp -f "$REPO_ROOT/src/_build/default/rustc_verifast/rustc_verifast.exe" "$REPO_ROOT/bin/rustc-verifast" 2>/dev/null || true
cp -f "$REPO_ROOT/src/_build/default/cargo_verifast/cargo_verifast.exe" "$REPO_ROOT/bin/cargo-verifast" 2>/dev/null || true
"$REPO_ROOT/scripts/vf_lock_run.sh" dune build --root "$REPO_ROOT/src" \
  coverage/vf_cov_report.exe coverage/cov_self_test.exe unit_tests/unit_tests.exe json_tests/json_tests.exe

if [ -d /tmp/vf_mut_bin ]; then
  cp -f "$REPO_ROOT/bin/verifast" "$REPO_ROOT/bin/refinement-checker" "$REPO_ROOT/bin/rustc-verifast" "$REPO_ROOT/bin/cargo-verifast" /tmp/vf_mut_bin/ 2>/dev/null || true
fi

echo "=== [2/4] Initializing Coverage Environment ==="
if [ "$MODE" = "full" ] || [ ! -d "$RAW_DIR" ]; then
  rm -rf "$RAW_DIR"
  mkdir -p "$RAW_DIR"
fi
mkdir -p "$OUT_DIR"

if [ "$RUST_COV" = true ]; then
  echo "--- Instrumenting vf-rust-mir-exporter with LLVM Source Coverage ---"
  pushd "$REPO_ROOT/src/rust_frontend/vf_mir_exporter" > /dev/null
  RUSTFLAGS="-C instrument-coverage" cargo +nightly-2026-09-25 build --quiet
  cp target/debug/vf_mir_exporter "$REPO_ROOT/bin/vf-rust-mir-exporter"
  popd > /dev/null
  export LLVM_PROFILE_FILE="$RAW_DIR/rust-%p-%m.profraw"
fi

export VF_COVERAGE_DIR="$RAW_DIR"

echo "=== [3/4] Executing Test Suites Under Coverage (mode: $MODE) ==="

echo "--- 3a. Running OCaml & JSON Unit Tests ---"
"$JSON_TEST_EXE"
"$UNIT_TEST_EXE"
verifast -c -allow_dead_code -disable_overflow_check "$REPO_ROOT/src/unit_tests/cov_exprs.c"
verifast -c -fno-strict-aliasing -uppercase_type_params_carry_typeid "$REPO_ROOT/tests/generic_structs.c"
verifast -c "$REPO_ROOT/tests/comma_expr.c" "$REPO_ROOT/tests/continue.c" "$REPO_ROOT/tests/floating_point.c" "$REPO_ROOT/tests/chars__of_struct.c" "$REPO_ROOT/examples/tutorial/lemptrs.c" "$REPO_ROOT/examples/leftpad.c" "$REPO_ROOT/examples/mutually_recursive_fns_simple.c" "$REPO_ROOT/examples/unions2.c"

if [ "$MODE" = "full" ]; then
  echo "--- Running Full VeriFast Test Suite (testsuite.mysh) ---"
  pushd "$REPO_ROOT" > /dev/null
  mysh -cpus 8 < testsuite.mysh
  popd > /dev/null
fi
  echo "--- 3b. Running C, C++, and Java Soundness Negative & Positive Suite ---"
  pushd "$REPO_ROOT/tests/soundness_c_cxx_java" > /dev/null
  mysh -cpus 8 < testsuite.mysh
  popd > /dev/null

  echo "--- 3b1. Running Z3v4.5 & S-Expression Emitter Invocations ---"
  verifast -c -prover z3v4.5 "$REPO_ROOT/tests/match_ctor_pat.c"
  verifast -c -emit_sexpr "$RAW_DIR/test1.sexpr" "$REPO_ROOT/tests/match_ctor_pat.c"
  verifast -c -emit_sexpr "$RAW_DIR/test2.sexpr" "$REPO_ROOT/examples/mutually_recursive_fns_simple.c"
  verifast -c -emit_sexpr "$RAW_DIR/test3.sexpr" "$REPO_ROOT/examples/leftpad.c"
  verifast -c -emit_sexpr "$RAW_DIR/test4.sexpr" "$REPO_ROOT/examples/tutorial/lemptrs.c"
  rm -f "$RAW_DIR"/test*.sexpr

  echo "--- 3b2. Running C++ Soundness & Verification Suite ---"
  verifast -c -target Linux64 "$REPO_ROOT/tests/cxx/literals.cpp"
  verifast -c -target Linux64 "$REPO_ROOT/tests/cxx/declarations.cpp"
  verifast -c -target Linux64 "$REPO_ROOT/tests/cxx/constructors.cpp"
  verifast -c -target Linux64 "$REPO_ROOT/tests/cxx/destructors.cpp"
  verifast -c -target Linux64 -disable_overflow_check "$REPO_ROOT/tests/cxx/references/lvalue_refs.cpp"
  verifast -c -target Linux64 "$REPO_ROOT/tests/cxx/virtual_methods/virtual_methods.cpp"
  verifast -c -target Linux64 "$REPO_ROOT/tests/cxx/loops.cpp"
  verifast -c -target Linux64 "$REPO_ROOT/tests/cxx/switch.cpp"
  verifast -c -target Linux64 -disable_overflow_check "$REPO_ROOT/tests/cxx/instance_preds/Stack.cpp"
  verifast -c -target Linux64 -disable_overflow_check "$REPO_ROOT/tests/cxx/instance_preds/Account.cpp"
  verifast -c -target Linux64 -disable_overflow_check "$REPO_ROOT/tests/cxx/instance_preds/Shape.cpp"
  verifast -c -target Linux64 -disable_overflow_check "$REPO_ROOT/tests/cxx/Overloads.cpp"
  verifast -c -target Linux64 -disable_overflow_check "$REPO_ROOT/tests/cxx/casts.cpp"

  echo "--- 3b3. Running Comprehensive Feature Coverage Suite (Redux, Java, C++, C Errors) ---"
  pushd "$REPO_ROOT/tests/copredicates" > /dev/null
  mysh < run.mysh
  popd > /dev/null

  verifast -c -prover redux -allow_should_fail "$REPO_ROOT"/tests/errors/redux*.c
  verifast -c -allow_should_fail -disable_overflow_check "$REPO_ROOT"/tests/errors/div_mod_by_zero.c "$REPO_ROOT"/tests/errors/shift_errors.c "$REPO_ROOT"/tests/errors/sizeof_signedness.c "$REPO_ROOT"/tests/errors/switch.c "$REPO_ROOT"/tests/errors/int_lit_overflow.c "$REPO_ROOT"/tests/errors/basics.c "$REPO_ROOT"/tests/errors/autoclose_bad_downcast.c "$REPO_ROOT"/tests/errors/ctor_pattern_upcast.c "$REPO_ROOT"/tests/errors/fraction-of-fraction.c "$REPO_ROOT"/tests/errors/ghost_assignment.c "$REPO_ROOT"/tests/errors/ghost_field.c "$REPO_ROOT"/tests/errors/ghost_hiding_real.c "$REPO_ROOT"/tests/errors/inductive_confusion.c "$REPO_ROOT"/tests/errors/inductive_welldefined.c "$REPO_ROOT"/tests/errors/inhabited.c "$REPO_ROOT"/tests/errors/inhabited_tparams.c "$REPO_ROOT"/tests/errors/predtype_contra.c
  verifast -c -allow_should_fail -allow_assume "$REPO_ROOT"/tests/errors/superctor.java "$REPO_ROOT"/tests/errors/override.java "$REPO_ROOT"/tests/errors/override2.java "$REPO_ROOT"/tests/errors/override3.java "$REPO_ROOT"/tests/errors/array_slice_autosplit.java "$REPO_ROOT"/tests/errors/array_update.java
  verifast -c -allow_should_fail "$REPO_ROOT"/tests/java/generics/BasicGenericClass.java "$REPO_ROOT"/tests/java/generics/CorrectFieldTypes.java "$REPO_ROOT"/tests/java/generics/DiamondOperator.java "$REPO_ROOT"/tests/java/generics/GenericInheritance.java "$REPO_ROOT"/tests/java/generics/GenericType.java "$REPO_ROOT"/tests/java/generics/MethodInference.java "$REPO_ROOT"/tests/java/generics/QualifiedGenericMethodCall.java
  verifast -c -disable_overflow_check -allow_should_fail "$REPO_ROOT"/examples/java/InstanceOf.java "$REPO_ROOT"/examples/java/Downcast.java "$REPO_ROOT"/examples/java/SuperCalls.java "$REPO_ROOT"/examples/java/DoWhile.java "$REPO_ROOT"/examples/java/CompoundAssignments.java "$REPO_ROOT"/examples/java/FieldInitializers.java "$REPO_ROOT"/examples/java/FloatingPoint.java "$REPO_ROOT"/examples/java/Constants.java "$REPO_ROOT"/examples/java/DefaultCtor.java "$REPO_ROOT"/examples/java/NestedExprTest.java "$REPO_ROOT"/examples/java/GenericClass.java
  verifast -c -target Linux64 -disable_overflow_check -allow_dead_code -allow_should_fail "$REPO_ROOT"/tests/cxx/inheritance/single_inheritance.cpp "$REPO_ROOT"/tests/cxx/inheritance/multiple_inheritance.cpp "$REPO_ROOT"/tests/cxx/inheritance/diamond.cpp "$REPO_ROOT"/tests/cxx/inheritance/method_call_in_dtor.cpp "$REPO_ROOT"/tests/cxx/delete/polymorphic.cpp "$REPO_ROOT"/tests/cxx/delete/non_polymorphic_base.cpp "$REPO_ROOT"/tests/cxx/delete/non_virtual_base_dtor.cpp "$REPO_ROOT"/tests/cxx/templates/function_template_general_contract.cpp "$REPO_ROOT"/tests/cxx/arrays.cpp "$REPO_ROOT"/tests/cxx/new_class.cpp "$REPO_ROOT"/tests/cxx/new_primitives.cpp "$REPO_ROOT"/tests/cxx/operators.cpp "$REPO_ROOT"/tests/cxx/typeid.cpp "$REPO_ROOT"/tests/cxx/ghost_field.cpp "$REPO_ROOT"/tests/cxx/main_implicit_return.cpp "$REPO_ROOT"/tests/cxx/non_compound_stmts.cpp
  verifast -c -disable_overflow_check -allow_should_fail "$REPO_ROOT"/tests/call_in_struct_init.c "$REPO_ROOT"/tests/check_expr_varargs.c "$REPO_ROOT"/tests/const_vars.c "$REPO_ROOT"/tests/declarators.c "$REPO_ROOT"/tests/deref_integer_.c "$REPO_ROOT"/tests/div.c "$REPO_ROOT"/tests/div_mod_negative_dividend.c "$REPO_ROOT"/tests/effective_types.c "$REPO_ROOT"/tests/evaluation_order_checks.c "$REPO_ROOT"/tests/generic_points_to.c "$REPO_ROOT"/tests/inductive_field_access.c "$REPO_ROOT"/tests/integral-ghost-types.c "$REPO_ROOT"/tests/alloc_zero.c "$REPO_ROOT"/tests/any_russell.c "$REPO_ROOT"/tests/any_russell2.c "$REPO_ROOT"/tests/any_russell3.c "$REPO_ROOT"/tests/issue110.c "$REPO_ROOT"/tests/issue112.c "$REPO_ROOT"/tests/issue206.c "$REPO_ROOT"/tests/issue238.c "$REPO_ROOT"/tests/issue247.c "$REPO_ROOT"/tests/issue309.c "$REPO_ROOT"/tests/issue310.c "$REPO_ROOT"/tests/issue311.c "$REPO_ROOT"/tests/issue357.c "$REPO_ROOT"/tests/issue507.c "$REPO_ROOT"/tests/issue511.c "$REPO_ROOT"/tests/issue513.c "$REPO_ROOT"/tests/issue536.c "$REPO_ROOT"/tests/issue601.c
  verifast -c -fwrapv "$REPO_ROOT"/tests/fwrapv.c

  echo "--- 3b4. Running VeriFast CLI Flags & Diagnostic Options ---"
  mkdir -p /tmp/vf_cov_dumps/asts /tmp/vf_cov_dumps/asts_locs
  verifast -c -stats "$REPO_ROOT/tests/comma_expr.c" > /dev/null
  verifast -c -json "$REPO_ROOT/tests/comma_expr.c" > /dev/null
  verifast -c -dump_ast /tmp/vf_cov_dumps/ast.txt "$REPO_ROOT/tests/comma_expr.c"
  verifast -c -dump_ast_with_locs /tmp/vf_cov_dumps/ast_locs.txt "$REPO_ROOT/tests/comma_expr.c"
  verifast -c -dump_asts /tmp/vf_cov_dumps/asts "$REPO_ROOT/tests/comma_expr.c"
  verifast -c -dump_asts_with_locs /tmp/vf_cov_dumps/asts_locs "$REPO_ROOT/tests/comma_expr.c"
  verifast -c -emit_highlighted_source_files "$REPO_ROOT/tests/comma_expr.c" > /dev/null
  verifast -c -dump_per_line_stmt_exec_counts "$REPO_ROOT/tests/comma_expr.c" > /dev/null
  verifast -c -verbose 4 -verbose_flag rust_exporter -verbose_flag type_pred_defs -verbose_flag specializer "$REPO_ROOT/tests/comma_expr.c" > /dev/null
  verifast -c -target IP16 "$REPO_ROOT/tests/comma_expr.c"
  verifast -c -target ILP32 "$REPO_ROOT/tests/comma_expr.c"
  verifast -c -target LLP64 "$REPO_ROOT/tests/comma_expr.c"
  verifast -c -target LP64 "$REPO_ROOT/tests/comma_expr.c"
  verifast -c -runtime "$REPO_ROOT/tests/comma_expr.c"
  verifast -c -assume_left_to_right_evaluation -assume_no_provenance -fno-strict-aliasing -assume_no_subobject_provenance "$REPO_ROOT/tests/comma_expr.c"
  verifast -c -allow_dead_code -focus "$REPO_ROOT/tests/comma_expr.c:5" "$REPO_ROOT/tests/comma_expr.c"
  verifast -c -allow_dead_code -breakpoint "$REPO_ROOT/tests/comma_expr.c:5" "$REPO_ROOT/tests/comma_expr.c" || true
  rm -rf /tmp/vf_cov_dumps comma_expr.html


echo "--- 3c. Running Rust Root & Soundness Negative Suite ---"
  pushd "$REPO_ROOT/tests/rust" > /dev/null
  verifast -allow_should_fail unsized_cast.rs
  verifast -allow_should_fail size_of_ptr_unsized.rs
  verifast - skip_specless_fns const_generic_param.rs 2>/dev/null || verifast -skip_specless_fns const_generic_param.rs
  verifast -allow_dead_code -allow_should_fail struct_layout.rs
  verifast ghost_cmd_inj.rs
  verifast parser_test.rs
  verifast ghost_while.rs
  verifast -allow_should_fail type_pred_defs_for_imported_structs.rs
  verifast -allow_should_fail duplicate_type_pred_defs.rs
  verifast -allow_should_fail -allow_assume preprocessor_test.rs
  verifast -allow_should_fail -allow_assume preprocessor_test_crlf.rs
  verifast -allow_should_fail -allow_assume preprocessor_test_crlf_bom.rs
  verifast -allow_should_fail pred_arg_lft.rs
  verifast -allow_should_fail -allow_dead_code lemma_without_body.rs
  verifast -allow_should_fail -allow_dead_code assume_stmt.rs
  verifast hidden_locals.rs
  verifast -allow_should_fail -allow_dead_code this_pred.rs
  verifast use_decls_in_modules.rs
  verifast -ignore_ref_creation -allow_assume nonnull.rs
  verifast -skip_specless_fns nonnull_into.rs
  verifast -allow_should_fail raw_slice_ptr_field.rs
  verifast -allow_should_fail unchecked_ops_and_shifts.rs
  verifast -allow_should_fail safe_abstraction/vec_deque_ring.rs
  verifast -apply_quick_fix safe_abstraction/proof_obligs_quick_fix_test_result.rs safe_abstraction/proof_obligs_quick_fix_test.rs
  verifast -allow_assume safe_abstraction/proof_obligs_quick_fix_test_result.rs
  rm -f safe_abstraction/proof_obligs_quick_fix_test_result.rs
  mysh -cpus 8 < testsuite.mysh
  popd > /dev/null

  echo "--- 3d. Running Full Refinement Checker Suite (87 runs) ---"
  pushd "$REPO_ROOT/tests/rust/refinement_checker" > /dev/null
  mysh -cpus 8 < testsuite.mysh
  refinement-checker --verbose 3 basic_orig.rs basic_verified.rs > /dev/null
  refinement-checker --verbose 3 structs_orig.rs structs_verified.rs > /dev/null
  refinement-checker --verbose 3 enums_orig.rs enums_verified.rs > /dev/null
  refinement-checker --verbose 3 loop_orig.rs loop_verified.rs > /dev/null
  refinement-checker --verbose 3 tuples_orig.rs tuples_verified.rs > /dev/null
  refinement-checker --verbose 3 rc_cov_arrays_slices_orig.rs rc_cov_arrays_slices_verified.rs > /dev/null
  refinement-checker --verbose 3 rc_cov_calls_closures_orig.rs rc_cov_calls_closures_verified.rs > /dev/null
  refinement-checker --verbose 3 rc_cov_directives_mut_orig.rs rc_cov_directives_mut_verified.rs > /dev/null
  popd > /dev/null

  echo "--- 3e. Running Rocq Consistency & -emit_rocq Validator ---"
  python3 "$REPO_ROOT/tests/rust/rocq_check.py"

  echo "--- 3f. Running Differential Testing vs Miri & rustc ---"
  python3 "$REPO_ROOT/tests/fuzz_diff_mutation/differential_miri_test.py"

  echo "--- 3g. Running Mutation Testing Suite (42 Mutants) ---"
  python3 "$REPO_ROOT/tests/fuzz_diff_mutation/mutation_test.py"

  echo "--- 3h. Running Grammar & Annotation Fuzzer (100 Iterations) ---"
  python3 "$REPO_ROOT/tests/fuzz_diff_mutation/fuzz_verifast.py" --seed 42 --iterations 100
unset VF_COVERAGE_DIR

if [ "$RUST_COV" = true ]; then
  echo "=== [4a/4] Generating Rust Frontend (vf_mir_exporter) Coverage Report ==="
  TOOLCHAIN_BIN="/home/devin/.rustup/toolchains/nightly-2026-09-25-x86_64-unknown-linux-gnu/lib/rustlib/x86_64-unknown-linux-gnu/bin"
  pushd "$REPO_ROOT/src/rust_frontend/vf_mir_exporter" > /dev/null
  RUSTFLAGS="-C instrument-coverage" LLVM_PROFILE_FILE="$RAW_DIR/rust-unit-%p-%m.profraw" cargo +nightly-2026-09-25 test --quiet
  "$TOOLCHAIN_BIN/llvm-profdata" merge -sparse "$RAW_DIR"/rust-*.profraw -o "$OUT_DIR/rust.profdata"
  TEST_BIN=$(find target/debug -type f -executable -name "vf_mir_exporter-*" | head -n 1)
  if [ -z "$TEST_BIN" ]; then
    TEST_BIN=$(find target/debug/build/vf_mir_exporter -type f -executable -name "vf_mir_exporter-*" | head -n 1)
  fi
  echo "--- Rust Coverage Summary (vf_mir_exporter) ---"
  if [ -n "$TEST_BIN" ]; then
    "$TOOLCHAIN_BIN/llvm-cov" report "$REPO_ROOT/bin/vf-rust-mir-exporter" -object "$TEST_BIN" \
      -instr-profile="$OUT_DIR/rust.profdata" --ignore-filename-regex="capnproto-rust|cargo/registry|rustup/toolchains|vf_mir_capnp.rs" | tee "$OUT_DIR/rust_coverage.txt"
  else
    "$TOOLCHAIN_BIN/llvm-cov" report "$REPO_ROOT/bin/vf-rust-mir-exporter" \
      -instr-profile="$OUT_DIR/rust.profdata" --ignore-filename-regex="capnproto-rust|cargo/registry|rustup/toolchains|vf_mir_capnp.rs" | tee "$OUT_DIR/rust_coverage.txt"
  fi
  popd > /dev/null
  unset LLVM_PROFILE_FILE
  pushd "$REPO_ROOT/src/rust_frontend/vf_mir_exporter" > /dev/null
  cargo +nightly-2026-09-25 build --quiet
  cp target/debug/vf_mir_exporter "$REPO_ROOT/bin/vf-rust-mir-exporter"
  popd > /dev/null
fi

echo "=== [4b/4] Generating OCaml Coverage Reports ==="
"$REPORT_EXE" \
  --cov-dir "$RAW_DIR" \
  --out-json "$OUT_DIR/summary.json" \
  --out-lcov "$OUT_DIR/lcov.info" \
  --out-md "$OUT_DIR/uncovered_branches.md"

echo ""
echo "Coverage artifacts successfully generated in: $OUT_DIR"
echo "  - Summary JSON:       $OUT_DIR/summary.json"
echo "  - LCOV Tracefile:     $OUT_DIR/lcov.info"
echo "  - Uncovered Branches: $OUT_DIR/uncovered_branches.md"
if [ "$RUST_COV" = true ]; then
  echo "  - Rust Profdata:      $OUT_DIR/rust.profdata"
  echo "  - Rust Coverage Text: $OUT_DIR/rust_coverage.txt"
fi
