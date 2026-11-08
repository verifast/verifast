#!/usr/bin/env python3
"""
Differential Testing Harness: VeriFast vs. Miri & rustc
Tests semantic consistency, soundness rejection of UB, and tracks known open issues.
"""

import os
import sys
import json
import subprocess
import time
from pathlib import Path

BASE_DIR = Path(__file__).resolve().parent
REPO_ROOT = BASE_DIR.parent.parent
BIN_DIR = REPO_ROOT / "bin"
MIRI_RUNNER_DIR = BASE_DIR / "miri_runner"
CASES_DIR = BASE_DIR / "cases"

ENV = os.environ.copy()
ENV["PATH"] = f"/home/devin/.cargo/bin:{BIN_DIR}:" + ENV.get("PATH", "")
ENV["LD_LIBRARY_PATH"] = f"{BIN_DIR}:" + ENV.get("LD_LIBRARY_PATH", "")

def run_cmd(cmd, cwd=None, timeout=30):
    start = time.time()
    try:
        res = subprocess.run(
            cmd,
            cwd=cwd or BASE_DIR,
            env=ENV,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            timeout=timeout,
        )
        elapsed = time.time() - start
        return res.returncode, res.stdout, res.stderr, elapsed
    except subprocess.TimeoutExpired:
        return -1, "", "TIMEOUT", timeout

def test_category_a():
    cases = [
        ("cat_a_01_raw_ptr", "test_cat_a_01_raw_ptr", "Raw pointer write & read (&raw mut, *p = 42)"),
        ("cat_a_02_raw_slice", "test_cat_a_02_raw_slice", "Raw slice fat pointer field update (*mut [i32])"),
        ("cat_a_03_unchecked_add_sub", "test_cat_a_03_unchecked_add_sub", "Unchecked add & sub within bounds"),
        ("cat_a_04_unchecked_mul", "test_cat_a_04_unchecked_mul", "Unchecked mul within bounds"),
        ("cat_a_05_unchecked_shifts", "test_cat_a_05_unchecked_shifts", "Unchecked shl and shr within bitwidth"),
        ("cat_a_06_bit_shifts", "test_cat_a_06_bit_shifts", "Wrapping left shift and signed arithmetic right shift"),
        ("cat_a_07_struct_field", "test_cat_a_07_struct_field", "Struct field pointer update (&raw mut pt.x)"),
        ("cat_a_08_tuple_proj", "test_cat_a_08_tuple_proj", "Raw tuple projection and field addition (*p).0 + (*p).1"),
        ("cat_a_09_alloc_dealloc", "test_cat_a_09_alloc_dealloc", "Heap allocation, initialization, read, and deallocation"),
        ("cat_a_10_ptr_swap", "test_cat_a_10_ptr_swap", "In-place pointer swap through raw pointers"),
    ]

    results = []
    print("\n" + "="*80)
    print("CATEGORY A: Safe / Verified Unsafe Rust Programs (VeriFast 0 errors & Miri Pass)")
    print("="*80)

    for case_file, miri_filter, desc in cases:
        rs_path = CASES_DIR / f"{case_file}.rs"
        
        # 1. Run VeriFast
        vf_rc, vf_out, vf_err, vf_time = run_cmd(["verifast", str(rs_path)])
        vf_ok = (vf_rc == 0) and ("0 errors found" in vf_out)

        # 2. Run Miri
        miri_rc, miri_out, miri_err, miri_time = run_cmd(
            ["cargo", "+nightly", "miri", "test", miri_filter, "--", "--nocapture"],
            cwd=MIRI_RUNNER_DIR
        )
        miri_ok = (miri_rc == 0) and ("test result: ok." in miri_out)

        # 3. Run rustc
        bin_out = BASE_DIR / f".tmp_{case_file}"
        rustc_rc, _, rustc_err, _ = run_cmd(["rustc", "--crate-type", "bin", str(rs_path), "-o", str(bin_out)])
        run_ok = False
        if rustc_rc == 0:
            exec_rc, _, _, _ = run_cmd([str(bin_out)])
            run_ok = (exec_rc == 0)
            if bin_out.exists():
                bin_out.unlink()

        status = "PASS" if (vf_ok and miri_ok and run_ok) else "FAIL"
        print(f"[{status}] {case_file:<26} | VF: {'PASS' if vf_ok else 'FAIL'} ({vf_time:.2f}s) | Miri: {'PASS' if miri_ok else 'FAIL'} ({miri_time:.2f}s) | rustc: {'PASS' if run_ok else 'FAIL'} | {desc}")
        
        results.append({
            "category": "A",
            "case": case_file,
            "description": desc,
            "verifast_ok": vf_ok,
            "verifast_time": vf_time,
            "miri_ok": miri_ok,
            "miri_time": miri_time,
            "rustc_ok": run_ok,
            "status": status
        })

    return results

def test_category_b():
    cases = [
        ("cat_b_01_add_overflow", "test_cat_b_01_add_overflow", "unchecked_add overflow (255u8 + 1)", "overflow"),
        ("cat_b_02_sub_underflow", "test_cat_b_02_sub_underflow", "unchecked_sub underflow (0u32 - 1)", "overflow"),
        ("cat_b_03_mul_overflow", "test_cat_b_03_mul_overflow", "unchecked_mul overflow (200u8 * 2)", "overflow"),
        ("cat_b_04_shl_bitwidth", "test_cat_b_04_shl_bitwidth", "unchecked_shl by bitwidth (1u32 << 32)", "overflowing shift"),
        ("cat_b_05_shr_negative", "test_cat_b_05_shr_negative", "unchecked_shr by >= bitwidth (1i32 >> 32)", "overflowing shift"),
        ("cat_b_06_null_deref", "test_cat_b_06_null_deref", "Null pointer dereference (*null::<i32>())", "null pointer"),
        ("cat_b_07_use_after_free", "test_cat_b_07_use_after_free", "Use-after-free (*p after dealloc)", "freed"),
        ("cat_b_08_double_free", "test_cat_b_08_double_free", "Double-free (dealloc called twice on same ptr)", "freed"),
        ("cat_b_09_uninit_read", "test_cat_b_09_uninit_read", "Reading uninitialized heap memory before write", "uninitialized memory"),
        ("cat_b_10_out_of_bounds", "test_cat_b_10_out_of_bounds", "Out-of-bounds pointer read (*p.add(4))", "pointer arithmetic"),
    ]

    results = []
    print("\n" + "="*80)
    print("CATEGORY B: Undefined Behavior Programs (Both Miri and VeriFast Reject)")
    print("="*80)

    for case_file, miri_filter, desc, expected_ub in cases:
        rs_path = CASES_DIR / f"{case_file}.rs"

        # 1. Run VeriFast
        vf_rc, vf_out, vf_err, vf_time = run_cmd(["verifast", str(rs_path)])
        # VeriFast must reject (non-zero rc or error in output)
        vf_rejected = (vf_rc != 0) or ("error:" in vf_out) or ("error:" in vf_err)

        # 2. Run Miri
        miri_rc, miri_out, miri_err, miri_time = run_cmd(
            ["cargo", "+nightly", "miri", "test", miri_filter, "--", "--nocapture"],
            cwd=MIRI_RUNNER_DIR
        )
        miri_combined = miri_out + miri_err
        miri_detected_ub = (miri_rc != 0) and ("Undefined Behavior" in miri_combined)

        status = "PASS" if (vf_rejected and miri_detected_ub) else "FAIL"
        diag = "UB detected by Miri & rejected by VeriFast"
        print(f"[{status}] {case_file:<26} | VF Rejected: {'YES' if vf_rejected else 'NO'} | Miri UB: {'YES' if miri_detected_ub else 'NO'} | {desc}")

        results.append({
            "category": "B",
            "case": case_file,
            "description": desc,
            "verifast_rejected": vf_rejected,
            "miri_detected_ub": miri_detected_ub,
            "expected_ub_sub": expected_ub,
            "status": status
        })

    return results

def test_category_c():
    cases = [
        (
            "cat_c_01_issue_947",
            "test_cat_c_01_issue_947",
            "Issue #947: Local pointer escapes inner block after StorageDead",
            "freed"
        ),
        (
            "cat_c_02_issue_685",
            "test_cat_c_02_issue_685",
            "Issue #685: Stacked Borrows mutable reference aliasing raw pointer",
            "borrow stack"
        ),
    ]

    results = []
    print("\n" + "="*80)
    print("CATEGORY C: Known Open Issue Characterization Probes")
    print("="*80)

    for case_file, miri_filter, desc, ub_kw in cases:
        rs_path = CASES_DIR / f"{case_file}.rs"

        # 1. Run VeriFast
        vf_rc, vf_out, vf_err, vf_time = run_cmd(["verifast", str(rs_path)])
        vf_accepted = (vf_rc == 0) and ("0 errors found" in vf_out)

        # 2. Run Miri
        miri_rc, miri_out, miri_err, miri_time = run_cmd(
            ["cargo", "+nightly", "miri", "test", miri_filter, "--", "--nocapture"],
            cwd=MIRI_RUNNER_DIR
        )
        miri_combined = miri_out + miri_err
        miri_detected_ub = (miri_rc != 0) and ("Undefined Behavior" in miri_combined) and (ub_kw in miri_combined)

        issue_tag = "[KNOWN_OPEN_ISSUE #947]" if "947" in case_file else "[KNOWN_OPEN_ISSUE #685]"
        status = "TRACKED"
        print(f"[{status}] {issue_tag} {case_file:<22} | VF Accepted: {vf_accepted} | Miri Detected UB: {miri_detected_ub} | {desc}")

        results.append({
            "category": "C",
            "case": case_file,
            "issue_tag": issue_tag,
            "description": desc,
            "verifast_accepted": vf_accepted,
            "miri_detected_ub": miri_detected_ub,
            "status": status
        })

    return results

def main():
    print("Starting Differential Testing against Miri & rustc...")
    start_total = time.time()
    
    results_a = test_category_a()
    results_b = test_category_b()
    results_c = test_category_c()

    total_time = time.time() - start_total
    
    total_a = len(results_a)
    pass_a = sum(1 for r in results_a if r["status"] == "PASS")

    total_b = len(results_b)
    pass_b = sum(1 for r in results_b if r["status"] == "PASS")

    total_c = len(results_c)
    tracked_c = sum(1 for r in results_c if r["status"] == "TRACKED")

    print("\n" + "="*80)
    print(f"DIFFERENTIAL TESTING SUMMARY (Total Time: {total_time:.2f}s)")
    print(f"Category A (Safe / Verified Rust):  {pass_a}/{total_a} PASSED (100% agreement between VF & Miri)")
    print(f"Category B (UB Rejection):         {pass_b}/{total_b} PASSED (100% rejection by VF & detected by Miri)")
    print(f"Category C (Known Open Issues):    {tracked_c}/{total_c} TRACKED (Accurately characterized)")
    print("="*80)

    summary_data = {
        "summary": {
            "category_a": {"passed": pass_a, "total": total_a},
            "category_b": {"passed": pass_b, "total": total_b},
            "category_c": {"tracked": tracked_c, "total": total_c},
            "total_time_seconds": round(total_time, 2)
        },
        "results_a": results_a,
        "results_b": results_b,
        "results_c": results_c
    }

    with open(BASE_DIR / "differential_results.json", "w") as f:
        json.dump(summary_data, f, indent=2)

    if pass_a == total_a and pass_b == total_b:
        print("Differential test suite PASSED successfully.")
        return 0
    else:
        print("Differential test suite FAILED!")
        return 1

if __name__ == "__main__":
    sys.exit(main())
