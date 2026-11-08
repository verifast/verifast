#!/usr/bin/env bash
set -e

DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" >/dev/null 2>&1 && pwd)"
export PATH="/home/devin/.cargo/bin:/tmp/vfdeps-adf88dc/bin:/home/devin/verifast-src/bin:$PATH"
export LD_LIBRARY_PATH="/home/devin/verifast-src/bin:$LD_LIBRARY_PATH"

echo "================================================================================"
echo "Workstream 6: Fuzzing, Mutation Testing, & Differential Testing Suite"
echo "Targeting: verifast, refinement-checker, rustc, and cargo +nightly miri"
echo "================================================================================"

echo ""
echo ">>> STEP 1: Differential Testing against Miri & rustc"
python3 "${DIR}/differential_miri_test.py"

echo ""
echo ">>> STEP 2: Mutation Testing (42 Mutants across Rust, C, & Refinement Checker)"
python3 "${DIR}/mutation_test.py"

echo ""
echo ">>> STEP 3: Grammar & Structure Fuzzer (100 Iterations)"
python3 "${DIR}/fuzz_verifast.py" --seed 42 --iterations 100

echo ""
echo ">>> STEP 4: Generating Consolidated REPORT.md"
python3 "${DIR}/generate_report.py"

echo ""
echo "================================================================================"
echo "ALL TESTS COMPLETED SUCCESSFULLY!"
echo "Consolidated Report written to: tests/fuzz_diff_mutation/REPORT.md"
echo "================================================================================"
