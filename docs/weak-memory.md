# Weak memory and atomics in VeriFast (design + pragmatic support)

Status: design document + a pragmatic, sequentially-consistent (SC) lowering of
C11/GCC atomics. This is **not** a sound relaxed-memory logic. Read the
"Soundness" section before relying on results for concurrent code.

## The goal and the hard truth

The motivating goal is to verify Linux-kernel components, many of which are
lock-free and rely on the kernel's relaxed-memory primitives: `READ_ONCE` /
`WRITE_ONCE`, `smp_mb` / `smp_rmb` / `smp_wmb`, `smp_load_acquire` /
`smp_store_release`, RCU, seqlocks, per-CPU atomics, and the C11/GCC atomic
builtins (`__atomic_*`, `__sync_*`, `_Atomic`).

A **sound** program logic for this — one that accounts for instruction
reordering and the absence of a global total order on memory events — is a
research-scale result, not an engineering task. The relevant literature is the
relaxed-separation-logic line: RSL/FSL, GPS/iGPS, Cosmo, and RustBelt-relaxed.
Bringing any of these to bear on real kernel code, soundly and at scale, is
multi-year work. This document does not pretend otherwise.

## What VeriFast already has (and it is sound)

VeriFast has a sound model for fine-grained concurrency built on **atomic
spaces** and **lemma-function-pointer chunks**, not on a relaxed-memory model:

- `atomic_space(inv)` (see `examples/tutorial/finegrained/threading.h`) packages
  a shared invariant that may be opened only for the duration of a single
  atomic operation (`open_atomic_space` / `close_atomic_space`).
- An atomic operation is verified by supplying a *safety proof* as a
  lemma-function-pointer chunk that opens the space, performs the logical
  transition while owning the resource, and closes it
  (`examples/tutorial/finegrained/finegrained.c`).

This is **sound under sequential consistency** (equivalently, it assumes the
hardware/compiler provide SC for the atomics in question, which is what
`memory_order_seq_cst` is meant to give). It does *not* model acquire/release or
relaxed orderings as weaker-than-SC; it treats the protected transition as
atomic and linearizable. For a large fraction of kernel code that uses
`seq_cst`-style synchronization or is reasoned about as linearizable, this is the
right and sound tool — it is just verbose.

The gap is that the **C11/GCC atomic surface syntax is not connected** to this
model: `__atomic_load_n`, `_Atomic int`, etc. are not understood by the
front-end at all.

## Pragmatic support implemented here

To unblock verification of atomic-using code (and to make the existing
atomic-space model reachable from real kernel syntax), the Clang front-end now:

1. **Accepts the atomic memory-order macros** (`__ATOMIC_RELAXED` … `__ATOMIC_SEQ_CST`)
   without tripping the context-free-macro soundness check.
2. **Desugars `_Atomic T` to `T`** (the underlying type), so atomic-typed
   declarations and struct fields parse.
3. **Lowers the common atomic builtins to their ordinary memory operations**
   (memory order ignored), via `AtomicExpr` handling:
   - `__atomic_load_n(p, o)`            → `*p`
   - `__atomic_store_n(p, v, o)`        → `*p = v`
   - `__atomic_fetch_add(p, v, o)`      → `*p += v`, **returning the old value**
   - `__atomic_add_fetch(p, v, o)`      → `*p += v`, returning the new value
   - …and the `sub`/`and`/`or`/`xor` variants, both `fetch_*` and `*_fetch`.
   - `__atomic_exchange*` and `__atomic_compare_exchange*` are **not** lowered
     (they require read-modify-write sequencing that does not map to a single
     VeriFast expression); they produce a clean "unsupported" error.

### Soundness of the pragmatic lowering

This lowering is the **SC, single-owner** interpretation. It is sound exactly
when the program is data-race-free under sequential consistency and the atomic
location is *owned* (its points-to chunk is held) at the point of access — i.e.
when you are reasoning about the atomic-using code **sequentially**. It is
**unsound** for genuinely concurrent, lock-free access to a shared atomic,
because:

- it ignores all memory ordering (treats every access as `seq_cst` *and* as if
  no reordering were possible), and
- it requires local ownership of the location, which a truly shared atomic does
  not have — those accesses must instead go through `atomic_space`.

In practice this means: the lowering lets you verify the *sequential* behaviour
of code that happens to use atomics, and catch ordinary (non-concurrency) bugs
in it. Sound verification of the concurrent behaviour still requires the
existing `atomic_space` machinery.

## Roadmap to real support (staged)

1. **Parse/lower surface syntax (done here).** C11/GCC atomics and `_Atomic`
   types are accepted and lowered under the SC/single-owner reading.
2. **Connect atomics to `atomic_space` (sound, engineering-scale).** Give the
   atomic builtins contracts expressed against `atomic_space`/lemma-pointer
   chunks, so `__atomic_*` on a *shared* location is verified soundly the way
   the finegrained example verifies `atomic_fetch_and_negate`. This is the
   highest-value next step: it makes real lock-free kernel code verifiable
   soundly under the SC assumption, from kernel syntax, without hand-rolling the
   plumbing per call site. Includes modelling `smp_*` barriers and
   `READ_ONCE`/`WRITE_ONCE` (the latter already lex via volatile + the inline-asm
   no-op/havoc work).
3. **Relaxed memory (research-scale).** Replace the SC assumption with a real
   relaxed-memory separation logic (FSL/GPS/Cosmo-style): per-location
   protocols, acquire/release resource transfer, release sequences, fence
   semantics. This is a research project; it should be scoped as such, with its
   own soundness proof, and is out of scope for the engineering effort here.

## Files

- `src/cxx_frontend/ast_translator.ml` — allow the `__ATOMIC_*` macros.
- `src/cxx_frontend/ast_exporter/TypeSerializer.cpp` — `_Atomic T` → `T`.
- `src/cxx_frontend/ast_exporter/ExprSerializer.cpp` — `VisitAtomicExpr`.
- `src/cxx_frontend/stubs/stubs_ast.capnp` — `Atomic` expression node.
- `src/cxx_frontend/expr_translator.ml` — lower atomics to ordinary ops.
