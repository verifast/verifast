# VeriFast Two-Tier Mutation Testing Report

## Executive Summary

- **Total Mutants Evaluated**: 150
- **Mutants Killed**: 150
- **Mutants Survived**: 0
- **Overall Mutation Test Strength**: **100.0%** (Target: >80%)

| Tier | Domain | Evaluated | Killed | Survived | Kill Rate | Target |
|:-----|:-------|:----------|:-------|:---------|:----------|:-------|
| **Tier 1** | Verifier Source-Level Logic | 60 | 60 | 0 | **100.0%** | >85% |
| **Tier 2** | Program, Spec & Refinement | 90 | 90 | 0 | **100.0%** | >90% |
| **Total** | **Combined Two-Tier Suite** | **150** | **150** | **0** | **100.0%** | **>80%** |

---

## Suite Breakdown

| Suite | Description | Mutants | Killed | Kill Rate |
|:------|:------------|:--------|:-------|:----------|
| `source_json` | VeriFast JSON Parser & Serializer | 8 | 8 | 100.0% |
| `source_sexpr` | VeriFast S-Expression Formatter | 8 | 8 | 100.0% |
| `source_aux` | VeriFast OCaml Utilities (`ocaml_aux.ml`) | 8 | 8 | 100.0% |
| `source_simplex` | VeriFast Linear Arithmetic Simplex Solver | 6 | 6 | 100.0% |
| `source_redux` | VeriFast Redux Built-in SMT/Congruence-Closure Prover | 10 | 10 | 100.0% |
| `source_loc` | VeriFast Source Location AST Utilities (`src_loc_aux.ml`) | 8 | 8 | 100.0% |
| `source_util` | VeriFast General Frontend Utilities (`util.ml`) | 6 | 6 | 100.0% |
| `source_z` | VeriFast Arbitrary-Precision Z Integer Operations (`z.ml`) | 6 | 6 | 100.0% |
| `rust_verifier` | Rust Safe Abstractions, Lifetimes, Borrows, Pointer Ops | 24 | 24 | 100.0% |
| `c_verifier` | C Separation Logic, Fractional Perms, Loops, Lemmas | 24 | 24 | 100.0% |
| `cxx_verifier` | C++ Inheritance, Constructors, Virtual Destructors | 10 | 10 | 100.0% |
| `java_verifier` | Java Class Invariants, Method Specs, Null Checks, Arrays | 10 | 10 | 100.0% |
| `refinement_checker` | Refinement Checker Soundness (Values, Drop, Effects) | 22 | 22 | 100.0% |

---

## Certification Status

- **Tier 1 (Source Mutants >= 55, Kill Rate > 85%)**: **PASS** (60/60 killed = 100.0%)
- **Tier 2 (Program Mutants >= 80, Kill Rate > 90%)**: **PASS** (90/90 killed = 100.0%)
- **Combined Mutation Test Strength > 80%**: **PASS** (150/150 killed = 100.0%)
