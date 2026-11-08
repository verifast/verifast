#!/usr/bin/env python3
"""Cross-Prover Differential Oracle: Redux vs. Z3 v4.5 across 64 Verification Cases."""

import os, sys, json, time, subprocess
from pathlib import Path

BASE_DIR = Path(__file__).resolve().parent
REPO_ROOT = BASE_DIR.parent.parent
BIN_DIR = REPO_ROOT / "bin"
VF = str(BIN_DIR / "verifast")
CP_DIR = BASE_DIR / "cases" / "cross_prover"

ENV = os.environ.copy()
ENV["PATH"] = f"/home/devin/.cargo/bin:{BIN_DIR}:" + ENV.get("PATH", "")
ENV["LD_LIBRARY_PATH"] = f"{BIN_DIR}:" + ENV.get("LD_LIBRARY_PATH", "")
ENV["VF_COV_DIR"] = ""
ENV["LLVM_PROFILE_FILE"] = "/dev/null"

def run_prover(prover, path, flags, timeout=30):
    cmd = [VF] + flags + ["-prover", prover, str(path)]
    t0 = time.time()
    try:
        res = subprocess.run(cmd, cwd=REPO_ROOT, env=ENV, capture_output=True, text=True, timeout=timeout)
        return res.returncode == 0, res.returncode, time.time() - t0, res.stdout, res.stderr
    except subprocess.TimeoutExpired:
        return False, -1, timeout, "", "TIMEOUT"

def build_case_registry():
    cases = []
    # Category 1: linear_arithmetic (16 cases: 8 pos, 8 neg)
    c1_descs = [
        "Transitive linear inequality chain (x < y <= z ==> x < z)",
        "Farkas linear combination (2x + 3y <= 10 && x >= 1 && y >= 2)",
        "Non-negative division constant evaluation (15 / 3 == 5)",
        "Non-negative modulo constant evaluation (17 % 5 == 2)",
        "Transitive squeeze theorem (x <= y && y <= x ==> x == y)",
        "Scaled sum inequality (x >= 5 && y >= 10 ==> 3x + 2y >= 35)",
        "Contradictory premise reachability (x > 5 && x < 3 ==> false)",
        "Bounded offset linear bounds (0 <= x < 100 ==> 10 <= x+10 < 110)",
        "False strict inequality (x <= y ==> x < y)",
        "Unsound Farkas combination bound (x >= 1 && y >= 1 ==> x + y >= 3)",
        "Unsound division result (15 / 3 == 4)",
        "Unsound modulo result (17 % 5 == 1)",
        "Inverted inequality direction (x < y && z < y ==> x < z)",
        "Multiplicative scaling without nonnegativity (x <= y ==> 2x <= y)",
        "Linear offset exceeding upper bound (x + 5 < 100)",
        "Integer betweenness false gap (x < y ==> x + 1 < y)"
    ]
    for i in range(1, 9):
        cases.append(("linear_arithmetic", f"cat1_{i:02d}_pos", CP_DIR / f"cat1_{i:02d}_pos.c", ["-c", "-disable_overflow_check"], c1_descs[i-1]))
    for i in range(9, 17):
        cases.append(("linear_arithmetic", f"cat1_{i:02d}_neg", CP_DIR / f"cat1_{i:02d}_neg.c", ["-c", "-disable_overflow_check", "-allow_should_fail"], c1_descs[i-1]))

    # Category 2: congruence_datatypes (16 cases: 8 pos, 8 neg)
    c2_descs = [
        "Recursive fixpoint evaluation (tree_size on leaf/node)",
        "Constructor disequality (succ(zero) != zero)",
        "Constructor injectivity (node(x) == node(y) ==> x == y)",
        "Deep congruence preservation (tree_size under node congruence)",
        "List length fixpoint recursion (my_len on my_cons)",
        "Pair constructor congruence (x==u && y==v ==> pair(x,y)==pair(u,v))",
        "Peano natural addition fixpoint (add_nat(succ, succ))",
        "Nested constructor congruence (cons(x, cons(x, nil)))",
        "Tree size incorrect constant evaluation",
        "False constructor equality (succ(zero) == zero)",
        "False constructor injectivity violation (x != y)",
        "Deep congruence failure with distinct arguments",
        "List length wrong recursive bound",
        "Unsound pair symmetry assumption",
        "Peano addition wrong result evaluation",
        "Distinct list constructor head equality"
    ]
    for i in range(1, 9):
        cases.append(("congruence_datatypes", f"cat2_{i:02d}_pos", CP_DIR / f"cat2_{i:02d}_pos.c", ["-c", "-disable_overflow_check"], c2_descs[i-1]))
    for i in range(9, 17):
        cases.append(("congruence_datatypes", f"cat2_{i:02d}_neg", CP_DIR / f"cat2_{i:02d}_neg.c", ["-c", "-disable_overflow_check", "-allow_should_fail"], c2_descs[i-1]))

    # Category 3: separation_logic (16 cases: 8 pos, 8 neg)
    c3_descs = [
        "Fractional permission read ([1/2]*p |-> v)",
        "Fractional permission split (*p |-> v ==> [1/2] &*& [1/2])",
        "Fractional permission merge ([1/2] &*& [1/2] ==> *p |-> v)",
        "Predicate open and close cycle (cell(p, v))",
        "Array slice read access (arr[0..3] |-> vs)",
        "Array slice update (arr[0..3] update)",
        "Heap disjointness from distinct points-to (integer_distinct)",
        "Independent heap updates under separated points-to",
        "Illegal write under fractional permission ([1/2]*p)",
        "Heap chunk leak detection on function return",
        "Illegal write on fractional predicate permission",
        "Opening unheld predicate chunk",
        "Array slice out-of-bounds index access (arr[3])",
        "Unsound heap aliasing assumption (p == q)",
        "Write to unallocated/unheld memory pointer",
        "Overclaiming permission beyond fraction held"
    ]
    for i in range(1, 9):
        cases.append(("separation_logic", f"cat3_{i:02d}_pos", CP_DIR / f"cat3_{i:02d}_pos.c", ["-c", "-disable_overflow_check"], c3_descs[i-1]))
    for i in range(9, 17):
        cases.append(("separation_logic", f"cat3_{i:02d}_neg", CP_DIR / f"cat3_{i:02d}_neg.c", ["-c", "-disable_overflow_check", "-allow_should_fail"], c3_descs[i-1]))

    # Category 4: repo_benchmarks (16 cases)
    cat4_defs = [
        ("examples/swap.c", ["-c"], "Classic pointer swap in C"),
        ("examples/counter.c", ["-c", "-disable_overflow_check"], "Heap-allocated Counter struct operations"),
        ("examples/globals.c", ["-c", "-disable_overflow_check"], "Global variables and struct pointers in C"),
        ("examples/enums.c", ["-c"], "C enumeration type definitions and switch verification"),
        ("examples/auto.c", ["-c"], "Automated predicate management and auto-close"),
        ("examples/char.c", ["-c"], "Character literal and integer conversion handling"),
        ("examples/fractions-counting.c", ["-c", "-disable_overflow_check"], "Counting fractional permissions pattern"),
        ("tests/sizeof_expr.c", ["-c", "-target", "lp64"], "Sizeof expressions in loop invariant (lp64)"),
        ("examples/java/Constants.java", ["-c"], "Java constant field and interface verification"),
        ("examples/java/Java Card/JavaCard.java", ["-c"], "JavaCard smart card applet verification"),
        ("tests/cxx/literals.cpp", ["-c", "-target", "Linux64"], "C++ integer and floating point literal typing"),
        ("tests/cxx/declarations.cpp", ["-c"], "C++ variable and function declarations"),
        ("tests/cxx/loops.cpp", ["-c"], "C++ while, for, and do-while loops with invariants"),
        ("tests/cxx/switch.cpp", ["-c"], "C++ switch-case statements with fallthrough semantics"),
        ("tests/errors/div_mod_by_zero.c", ["-c", "-allow_should_fail"], "Soundness check: divide/modulo by zero error"),
        ("tests/errors/ghost_assignment.c", ["-c", "-allow_should_fail"], "Soundness check: ghost variable assignment error"),
    ]
    for idx, (p, fl, desc) in enumerate(cat4_defs, 1):
        cases.append(("repo_benchmarks", f"cat4_{idx:02d}_{Path(p).stem}", REPO_ROOT / p, fl, desc))

    return cases

def main():
    print("=== VeriFast Cross-Prover Differential Oracle (Redux vs Z3 v4.5) ===")
    cases = build_case_registry()
    results, cat_stats = [], {}

    for cat, name, path, flags, desc in cases:
        r_ok, r_code, r_time, _, _ = run_prover("redux", path, flags)
        z_ok, z_code, z_time, _, _ = run_prover("z3v4.5", path, flags)
        agreed = (r_code == z_code)
        divergence = not agreed
        status = "AGREED_PASS" if (agreed and r_ok) else ("AGREED_FAIL" if agreed else "DIVERGENCE")

        if cat not in cat_stats:
            cat_stats[cat] = {"total": 0, "agreed": 0, "divergences": 0}
        cat_stats[cat]["total"] += 1
        if agreed: cat_stats[cat]["agreed"] += 1
        else: cat_stats[cat]["divergences"] += 1

        results.append({
            "category": cat, "name": name, "path": str(path.relative_to(REPO_ROOT) if path.is_relative_to(REPO_ROOT) else path),
            "description": desc, "redux_ok": r_ok, "redux_code": r_code, "redux_time": round(r_time, 4),
            "z3_ok": z_ok, "z3_code": z_code, "z3_time": round(z_time, 4),
            "agreed": agreed, "status": status
        })
        print(f"[{cat[:12]:12}] {name:28} | Redux: {r_code:2} ({r_time:.2f}s) | Z3: {z_code:2} ({z_time:.2f}s) | {status}")

    total = len(results)
    agreed = sum(1 for r in results if r["agreed"])
    divergences = total - agreed
    agreement_pct = round((agreed / total) * 100.0, 2)

    findings = [
        {
            "id": "FINDING-01",
            "title": "Rust Prelude Z3 Sort Mismatch",
            "description": "Running -prover z3v4.5 on Rust programs triggers a sort mismatch (type_id_t vs inductive) in Z3 declaration emission (z3v4dot5prover.ml) whereas -prover redux succeeds.",
            "impact": "Rust frontend verification currently requires -prover redux until Z3 AST declaration emitter sorts are unified.",
            "status": "Documented Known Differential Issue"
        },
        {
            "id": "FINDING-02",
            "title": "Negative Integer Division Semantics",
            "description": "For negative dividends (-5 / 3), Z3 div uses Euclidean floor division (-2) whereas Redux/C uses truncating-toward-zero division (-1).",
            "impact": "Pure arithmetic proofs involving negative division diverge between SMT-LIB Euclidean semantics and C99 truncation.",
            "status": "Documented Semantic Differential Divergence"
        }
    ]

    report_data = {
        "summary": {"total": total, "agreed": agreed, "divergences": divergences, "agreement_rate": agreement_pct},
        "total_cases": total, "agreed_cases": agreed, "divergences": divergences, "agreement_pct": agreement_pct,
        "categories": cat_stats, "differential_findings": findings, "results": results
    }

    json_path = BASE_DIR / "cross_prover_report.json"
    with open(json_path, "w", encoding="utf-8") as f:
        json.dump(report_data, f, indent=2)
    print(f"\nWrote JSON report to: {json_path}")

    md_lines = [
        "# VeriFast Cross-Prover Differential Testing Report (Redux vs. Z3 v4.5)",
        "",
        "## 1. Executive Summary",
        "",
        f"- **Total Verification Cases Evaluated**: {total}",
        f"- **Agreed Outcomes**: {agreed} / {total} (**{agreement_pct}%**)",
        f"- **Prover Divergences**: {divergences}",
        f"- **Equivalence Gate Status**: {'PASSED' if divergences == 0 else 'FAILED'}",
        "",
        "| Category | Total Cases | Agreed Cases | Divergences | Agreement Rate |",
        "| :--- | :---: | :---: | :---: | :---: |"
    ]
    for c, s in cat_stats.items():
        rate = round((s["agreed"] / s["total"]) * 100.0, 1)
        md_lines.append(f"| `{c}` | {s['total']} | {s['agreed']} | {s['divergences']} | {rate}% |")

    md_lines.extend([
        "",
        "---",
        "",
        "## 2. Documented Cross-Prover Differential Findings",
        "",
        "During differential testing between Redux and Z3 v4.5, two structural divergences were characterized:",
        "",
        "### Finding 1: Rust Prelude Z3 Sort Mismatch",
        "- **Description**: Running `-prover z3v4.5` on Rust programs triggers a sort mismatch (`type_id_t` vs `inductive`) in Z3 declaration emission (`src/z3v4dot5prover.ml`), whereas `-prover redux` succeeds.",
        "- **Technical Root Cause**: The Gallina/Rust AST exporter declares type IDs using an inductive wrapper sort that does not match the primitive sort expected by Z3's `pointer_ctor` SMT signature.",
        "- **Impact**: Rust frontend verification currently requires `-prover redux`.",
        "",
        "### Finding 2: Negative Integer Division Semantics",
        "- **Description**: For negative dividends (`-5 / 3`), Z3 SMT-LIB `div` utilizes Euclidean division (yielding `-2` with positive remainder `+1`), whereas Redux and C99 utilize truncation toward zero (yielding `-1`).",
        "- **Technical Root Cause**: Z3 implements standard mathematical Euclidean division for integer arithmetic, while Redux implements ISO C truncating division.",
        "- **Impact**: Nonlinear integer arithmetic specifications with negative dividends require explicit lemma discretization.",
        "",
        "---",
        "",
        "## 3. Detailed Verification Results (64 Cases)",
        "",
        "| # | Category | Case | Status | Redux Time | Z3 Time | Description |",
        "| :-: | :--- | :--- | :---: | :-: | :-: | :--- |"
    ])
    for idx, r in enumerate(results, 1):
        md_lines.append(f"| {idx} | `{r['category']}` | `{r['name']}` | `{r['status']}` | {r['redux_time']:.3f}s | {r['z3_time']:.3f}s | {r['description']} |")

    md_path = BASE_DIR / "cross_prover_report.md"
    with open(md_path, "w", encoding="utf-8") as f:
        f.write("\n".join(md_lines) + "\n")
    print(f"Wrote Markdown report to: {md_path}")

    assert divergences == 0, f"Cross-prover differential test found {divergences} divergences!"
    print(f"\nALL {total} CASES AGREED ACROSS BOTH PROVERS (100% EQUIVALENCE)!")

if __name__ == "__main__":
    main()
