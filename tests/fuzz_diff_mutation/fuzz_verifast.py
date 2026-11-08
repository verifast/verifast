#!/usr/bin/env python3
"""
Grammar & Structure Fuzzer for VeriFast & Refinement Checker
Generates tricky, malformed, and boundary-probing C, C++, Java, and Rust programs.
Verifies robust error handling: 0 crashes (SIGSEGV/SIGABRT) and 0 uncaught OCaml/Rust exceptions.
"""

import os
import sys
import json
import random
import argparse
import tempfile
import subprocess
import time
from pathlib import Path

BASE_DIR = Path(__file__).resolve().parent
REPO_ROOT = BASE_DIR.parent.parent
BIN_DIR = REPO_ROOT / "bin"

ENV = os.environ.copy()
cargo_bin = Path.home() / ".cargo" / "bin"
devin_cargo = Path("/home/devin/.cargo/bin")
cargo_paths = [str(cargo_bin)]
if devin_cargo.exists() and devin_cargo != cargo_bin:
    cargo_paths.append(str(devin_cargo))
ENV["PATH"] = ":".join(cargo_paths) + f":{BIN_DIR}:" + ENV.get("PATH", "")
ENV["LD_LIBRARY_PATH"] = f"{BIN_DIR}:" + ENV.get("LD_LIBRARY_PATH", "")

UNCAUGHT_EXCEPTION_PATTERNS = [
    "Assert_failure",
    "Match_failure",
    "Invalid_argument",
    "Stack_overflow",
    "Out_of_memory",
    "Failure(\"TODO\")",
    "panicked at",
    "Segmentation fault",
    "core dumped"
]

def run_cmd(cmd, timeout=5.0):
    start = time.time()
    try:
        res = subprocess.run(
            cmd,
            env=ENV,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            timeout=timeout,
        )
        elapsed = time.time() - start
        return res.returncode, res.stdout, res.stderr, elapsed, False
    except subprocess.TimeoutExpired:
        elapsed = time.time() - start
        return -999, "", "TIMEOUT", elapsed, True

# ==============================================================================
# INPUT GENERATORS
# ==============================================================================

def gen_extreme_integers(rng):
    int_literals = [
        "0xffffffffffffffffffffffffffffffff",
        "0x7fffffffffffffffffffffffffffffff",
        "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
        "170141183460469231731687303715884105728",
        "-170141183460469231731687303715884105729",
        "340282366920938463463374607431768211456",
        "999999999999999999999999999999999999999999999999999999999999",
        "-9223372036854775809",
        "18446744073709551616",
        "0",
        "-0",
        "000000000000000000000000000000000000000000000000000000000001"
    ]
    lit = rng.choice(int_literals)
    code = f"""
int test_ext_int()
    //@ requires true;
    //@ ensures true;
{{
    long long x = {lit};
    return 0;
}}
"""
    return "c", code, f"Extreme integer literal: {lit[:30]}"

def gen_deeply_nested_ghost(rng):
    depth = rng.randint(10, 40)
    nested_expr = "true"
    for _ in range(depth):
        op = rng.choice(["&&", "||", "== true ? true :", "&*&"])
        if op == "&*&":
            nested_expr = f"(emp &*& {nested_expr})"
        elif "?" in op:
            nested_expr = f"(true ? {nested_expr} : false)"
        else:
            nested_expr = f"({nested_expr} {op} true)"

    code = f"""
void test_deep_ghost()
    //@ requires {nested_expr};
    //@ ensures {nested_expr};
{{
}}
"""
    return "c", code, f"Deeply nested ghost specification (depth {depth})"

def gen_unclosed_ghost_comments(rng):
    variants = [
        "/*@ requires true;",
        "/*@ requires *p |-> _; /*@ ensures true; @*/",
        "/*@\npredicate test() = true;\n",
        "int foo() { /*@ return 0; }",
        "/*@ @*/ /*@ /*@ /*@ req true; @*/",
        "//@ req true;\n/*@ ens true;\nvoid bar() {}",
    ]
    v = rng.choice(variants)
    code = f"""
int x = 42;
{v}
int main() {{ return 0; }}
"""
    return "c", code, "Malformed / unclosed ghost comment sequence"

def gen_utf8_bom_crlf(rng):
    bom = b"\xef\xbb\xbf" if rng.random() > 0.5 else b""
    unicode_idents = ["????_??????????", "???????_????????", "?_var", "?_beta_?", "??_ferris", "?spec?"]
    ident = rng.choice(unicode_idents)
    nl = "\r\n" if rng.random() > 0.5 else "\n"
    
    text = f"""// UTF-8 test with strange identifiers and line endings{nl}int {ident} = 100;{nl}/*@ req true; @*/{nl}int test_unicode() {{{nl}    return {ident};{nl}}}{nl}"""
    raw_bytes = bom + text.encode("utf-8")
    return "raw_c", raw_bytes, f"UTF-8 BOM / Unicode identifier: {ident}"

def gen_ghost_keywords_combinatorics(rng):
    keywords = [
        "open test();",
        "close test();",
        "assert true;",
        "leak true;",
        "produce_lemma_function_pointer_chunk(0) {};",
        "consume_box_predicate;",
        "open_module;",
        "close_module;"
    ]
    picked = [rng.choice(keywords) for _ in range(rng.randint(3, 8))]
    body = "\n    //@ ".join(picked)
    code = f"""
/*@ predicate test() = true; @*/
void test_keywords()
    //@ requires test();
    //@ ensures true;
{{
    //@ {body}
}}
"""
    return "c", code, "Ghost keyword permutations (open/close/assert/leak/produce)"

def gen_rust_nested_mir(rng):
    depth = rng.randint(2, 6)
    tuple_ty = "i32"
    tuple_val = "0"
    for i in range(depth):
        tuple_ty = f"({tuple_ty}, i32)"
        tuple_val = f"({tuple_val}, {i})"

    code = f"""// verifast_options{{skip_specless_fns}}
pub unsafe fn test_nested_tuples() -> i32
//@ req true;
//@ ens true;
{{
    let t: {tuple_ty} = {tuple_val};
    let p = &raw const t;
    42
}}
fn main() {{}}
"""
    return "rs", code, f"Rust deeply nested tuple hierarchy (depth {depth})"

def gen_rust_raw_pointer_casts(rng):
    depth = rng.randint(2, 5)
    ptr_ty = "i32"
    for _ in range(depth):
        ptr_ty = f"*mut {ptr_ty}"

    code = f"""// verifast_options{{skip_specless_fns}}
pub unsafe fn test_pointer_cast_chains()
//@ req true;
//@ ens true;
{{
    let mut x: i32 = 10;
    let p = &raw mut x;
    let q = p as {ptr_ty};
}}
fn main() {{}}
"""
    return "rs", code, f"Rust multiple raw pointer deref/cast chain ({depth} levels)"

def gen_rust_refinement_pair(rng):
    num_stmts = rng.randint(1, 4)
    stmts_orig = []
    stmts_verif = []
    for i in range(num_stmts):
        val = rng.randint(1, 100)
        stmts_orig.append(f"x += {val};")
        if rng.random() > 0.5:
            stmts_verif.append(f"x += {val};")
        else:
            stmts_verif.append(f"x = x.wrapping_add({val});")

    code_orig = f"""
fn compute(mut x: i32) -> i32 {{
    {chr(10).join(stmts_orig)}
    x
}}
"""
    code_verif = f"""
fn compute(mut x: i32) -> i32 {{
    {chr(10).join(stmts_verif)}
    x
}}
"""
    return "refine_pair", (code_orig, code_verif), f"Refinement checker differential probe ({num_stmts} stmts)"

def gen_cpp_classes(rng):
    code = """
struct Point {
    int x;
    int y;
    /*@
    predicate valid() = this->x |-> ?vx &*& this->y |-> ?vy;
    @*/
    Point(int x0, int y0)
        //@ requires true;
        //@ ensures valid();
    {
        this->x = x0;
        this->y = y0;
        //@ close valid();
    }
};
"""
    return "cpp", code, "C++ struct with constructor and instance predicate"

def gen_java_class(rng):
    code = """
class FuzzAccount {
    int balance;
    //@ predicate valid() = this.balance |-> ?b &*& 0 <= b;

    FuzzAccount(int b)
        //@ requires 0 <= b;
        //@ ensures valid();
    {
        this.balance = b;
        //@ close valid();
    }
}
"""
    return "java", code, "Java class with predicate and constructor specification"

GENERATORS = [
    gen_extreme_integers,
    gen_deeply_nested_ghost,
    gen_unclosed_ghost_comments,
    gen_utf8_bom_crlf,
    gen_ghost_keywords_combinatorics,
    gen_rust_nested_mir,
    gen_rust_raw_pointer_casts,
    gen_rust_refinement_pair,
    gen_cpp_classes,
    gen_java_class
]

def run_fuzzer(seed=42, iterations=100, timeout=5.0):
    print("="*80)
    print(f"GRAMMAR & STRUCTURE FUZZER (Seed: {seed}, Iterations: {iterations})")
    print("Testing C, C++, Java, Rust, and Refinement-Checker across extreme/malformed inputs.")
    print("Soundness Requirement: 0 crashes / 0 uncaught OCaml or Rust exceptions.")
    print("="*80)

    rng = random.Random(seed)
    results = []
    crashes = []
    uncaught_exceptions = []
    timeouts = []

    start_time = time.time()

    for idx in range(1, iterations + 1):
        gen_fn = rng.choice(GENERATORS)
        kind, payload, desc = gen_fn(rng)

        # Execute test based on kind
        is_crash = False
        uncaught_sig = None
        out_snippet = ""
        dur = 0.0

        if kind == "refine_pair":
            orig_src, verif_src = payload
            with tempfile.NamedTemporaryFile("w", suffix=".rs", delete=False) as f1, \
                 tempfile.NamedTemporaryFile("w", suffix=".rs", delete=False) as f2:
                f1.write(orig_src)
                f2.write(verif_src)
                f1_path = f1.name
                f2_path = f2.name

            try:
                rc, stdout, stderr, dur, timed_out = run_cmd(["refinement-checker", f1_path, f2_path], timeout=timeout)
                combined = stdout + stderr
                out_snippet = combined.strip().replace("\n", " ")[:60]

                if timed_out:
                    timeouts.append(idx)
                elif rc < 0 or rc in (134, 139):
                    is_crash = True
                    crashes.append((idx, kind, desc, rc, out_snippet))
                else:
                    for pat in UNCAUGHT_EXCEPTION_PATTERNS:
                        if pat in combined:
                            uncaught_sig = pat
                            uncaught_exceptions.append((idx, kind, desc, pat, out_snippet))
                            break
            finally:
                if os.path.exists(f1_path): os.unlink(f1_path)
                if os.path.exists(f2_path): os.unlink(f2_path)

        elif kind == "raw_c":
            with tempfile.NamedTemporaryFile("wb", suffix=".c", delete=False) as f:
                f.write(payload)
                tf_path = f.name
            try:
                rc, stdout, stderr, dur, timed_out = run_cmd(["verifast", "-c", tf_path], timeout=timeout)
                combined = stdout + stderr
                out_snippet = combined.strip().replace("\n", " ")[:60]

                if timed_out:
                    timeouts.append(idx)
                elif rc < 0 or rc in (134, 139):
                    is_crash = True
                    crashes.append((idx, kind, desc, rc, out_snippet))
                else:
                    for pat in UNCAUGHT_EXCEPTION_PATTERNS:
                        if pat in combined:
                            uncaught_sig = pat
                            uncaught_exceptions.append((idx, kind, desc, pat, out_snippet))
                            break
            finally:
                if os.path.exists(tf_path): os.unlink(tf_path)

        else:
            suffix_map = {"c": ".c", "cpp": ".cpp", "java": ".java", "rs": ".rs"}
            suffix = suffix_map.get(kind, ".c")
            flags = ["-c"]

            with tempfile.NamedTemporaryFile("w", suffix=suffix, delete=False) as f:
                f.write(payload)
                tf_path = f.name

            try:
                rc, stdout, stderr, dur, timed_out = run_cmd(["verifast"] + flags + [tf_path], timeout=timeout)
                combined = stdout + stderr
                out_snippet = combined.strip().replace("\n", " ")[:60]

                if timed_out:
                    timeouts.append(idx)
                elif rc < 0 or rc in (134, 139):
                    is_crash = True
                    crashes.append((idx, kind, desc, rc, out_snippet))
                else:
                    for pat in UNCAUGHT_EXCEPTION_PATTERNS:
                        if pat in combined:
                            uncaught_sig = pat
                            uncaught_exceptions.append((idx, kind, desc, pat, out_snippet))
                            break
            finally:
                if os.path.exists(tf_path): os.unlink(tf_path)

        status = "CRASH" if is_crash else ("EXCEPTION" if uncaught_sig else ("TIMEOUT" if dur >= timeout else "OK"))
        if idx <= 20 or is_crash or uncaught_sig or idx % 10 == 0:
            print(f"[{status:^9}] Iter {idx:03d} | {kind.upper():<11} | {dur:.2f}s | {desc:<45} | {out_snippet}")

        results.append({
            "iteration": idx,
            "kind": kind,
            "description": desc,
            "status": status,
            "duration": dur,
            "snippet": out_snippet
        })

    total_time = time.time() - start_time
    total_crashes = len(crashes)
    total_exceptions = len(uncaught_exceptions)
    total_timeouts = len(timeouts)

    print("\n" + "="*80)
    print("FUZZER EXECUTION SUMMARY")
    print(f"Total Iterations:             {iterations}")
    print(f"Total Wall-Clock Time:        {total_time:.2f}s (Average {total_time/iterations*1000:.1f}ms/test)")
    print(f"Signals / Native Crashes:     {total_crashes}")
    print(f"Uncaught Internal Exceptions: {total_exceptions}")
    print(f"Timeouts (> {timeout}s):            {total_timeouts}")
    print(f"Gracefully Handled Inputs:    {iterations - total_crashes - total_exceptions - total_timeouts} / {iterations}")
    print("="*80)

    summary_data = {
        "summary": {
            "seed": seed,
            "iterations": iterations,
            "total_time_seconds": round(total_time, 2),
            "crashes": total_crashes,
            "uncaught_exceptions": total_exceptions,
            "timeouts": total_timeouts,
            "graceful_handled": iterations - total_crashes - total_exceptions - total_timeouts
        },
        "crashes": crashes,
        "uncaught_exceptions": uncaught_exceptions,
        "results": results
    }

    with open(BASE_DIR / "fuzz_results.json", "w") as f:
        json.dump(summary_data, f, indent=2)

    if total_crashes == 0 and total_exceptions == 0:
        print("Fuzzer verification PASSED: 0 crashes and 0 uncaught exceptions!")
        return 0
    else:
        print(f"Fuzzer discovered {total_crashes} crashes and {total_exceptions} uncaught exceptions!")
        return 1

def main():
    parser = argparse.ArgumentParser(description="Grammar and Structure Fuzzer for VeriFast")
    parser.add_argument("--seed", type=int, default=42, help="Deterministic random seed")
    parser.add_argument("--iterations", type=int, default=100, help="Number of test iterations")
    parser.add_argument("--timeout", type=float, default=5.0, help="Per-test timeout in seconds")
    args = parser.parse_args()

    return run_fuzzer(seed=args.seed, iterations=args.iterations, timeout=args.timeout)

if __name__ == "__main__":
    sys.exit(main())
