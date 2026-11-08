#!/usr/bin/env bash
set -e

DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" >/dev/null 2>&1 && pwd)"
REPO_ROOT="$(cd "$DIR/../.." && pwd)"
if [ -f "$REPO_ROOT/config.sh" ]; then
  . "$REPO_ROOT/config.sh"
fi
VFDEPS="/tmp/${VFDEPS_NAME:-vfdeps-adf88dc}"
CARGO_PATHS="$HOME/.cargo/bin"
if [ -d "/home/devin/.cargo/bin" ] && [ "$HOME/.cargo/bin" != "/home/devin/.cargo/bin" ]; then
  CARGO_PATHS="$CARGO_PATHS:/home/devin/.cargo/bin"
fi
export PATH="$CARGO_PATHS:$VFDEPS/bin:$REPO_ROOT/bin:$PATH"
export LD_LIBRARY_PATH="$REPO_ROOT/bin:${LD_LIBRARY_PATH:-}"

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
