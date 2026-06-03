# VeriFast annotation ergonomics: assessment + production-grade roadmap

Goal context: drive VeriFast with **LLM-written annotations** to verify Linux
kernel components. This document assesses how painful the annotation surface is
today, what already mitigates it, and what to build to make it production-grade
for an LLM-in-the-loop workflow.

## Evidence (measured, not impression)

- In the *expert-written* tutorial solutions, annotations are ~**30%** of all
  lines for data-structure code (`dispose.c` 28%, `filter.c`/`map.c`/`foreach.c`
  ~29%, `byref.c` 32%). `examples/stack.c`: 90 annotation lines / 468.
- Concrete shape — `tutorial_solutions/dispose.c`, `stack_is_empty`:

  ```c
  bool stack_is_empty(struct stack *stack)
      //@ requires stack(stack, ?count);
      //@ ensures stack(stack, count) &*& result == (count == 0);
  {
      //@ open stack(stack, count);          // ceremony
      struct node *head = stack->head;
      //@ open nodes(head, count);           // ceremony
      bool result = stack->head == 0;
      //@ close nodes(head, count);          // ceremony
      //@ close stack(stack, count);         // ceremony
      return result;
  }
  ```
  **4 of 7 body lines are `open`/`close` ceremony** for 3 lines of real code.

## What's painful (ranked by impact)

1. **`open`/`close` ceremony — the dominant cost.** Roughly half of all
   annotation lines in the corpus are manual `open`/`close`, plus the manual
   arithmetic threaded through them (`count`, `count+1`, `count-1`). This is
   mechanical, repetitive, and exactly what an LLM gets subtly wrong (wrong
   predicate, wrong args, off-by-one count).
2. **Hand-written struct predicates.** For each struct you write a
   points-to-all-fields predicate including the auto-generated
   `malloc_block_<s>`. Pure boilerplate, re-derived per type.
3. **Manual ghost arithmetic / lemma threading.** Counts, lengths, list models
   threaded by hand; nonlinear arithmetic and list lemmas often need explicit
   `lemma`/`fixpoint` + induction the user must author.
4. **Lemma / fixpoint / induction boilerplate** for anything the SMT solver
   won't do automatically.
5. **Weak feedback loop.** Errors like `No matching heap chunks: nodes(head, _)`
   or `Cannot prove condition` are accurate but rarely say *what annotation to
   add*. The machinery for actionable fixes exists (see below) but is barely
   populated — so an LLM can't reliably self-correct from the message.
6. **Mandatory contracts** on every verified function (partly mitigated by
   `-skip_specless_fns`, the default for C).
7. **Higher-order specs** (predicate families / predicate constructors / lemma
   function pointers) are powerful but verbose and hard for an LLM to get right
   — and they're exactly what concurrency (`atomic_space`) needs.
8. **No spec/loop-invariant inference.** Loop invariants are written by hand;
   there is no bi-abduction (à la Infer) to synthesize pre/post or frames.
9. **Syntax surface**: `?x` binders, `_` wildcards, `&*&`, fractional perms
   `[f]p`. Learnable, but more for an LLM to get exactly right.

## What already mitigates it (and is under-used)

- **Precise predicates + auto-open/close.** A predicate written with a
  semicolon separating *input* from *output* params —
  `predicate tree(struct tree *t; int depth) = ...` (see
  `tutorial_solutions/precise.c`) — is *precise*: the inputs determine the
  chunk, so the verifier can **auto-open and auto-close** it during chunk lookup
  (the "rules" path, `verify_expr.ml`). Most of `dispose.c`'s manual `open`/
  `close` disappears if `nodes`/`stack` are made precise. This is the single
  biggest existing lever and it is neither the default taught nor consistently
  used in examples.
- **`_auto` lemmas / `fixpoint_auto`** are applied automatically by the prover,
  removing manual lemma calls for common rewrites.
- **Quick-fix + help-topic infrastructure**: errors can carry a `help_topic` and
  machine-readable `QuickFix (description, InsertTextAt(loc, text))`, surfaced
  via `-json` and applied via `-apply_quick_fix`. Today it's populated at
  essentially one site — the capability is there, the content isn't.
- **`-json`** structured results: ideal for an LLM loop, already present.

## What to build (ranked by ROI), and how

### Phase 1 — ergonomic quick wins (low risk, days)
1. **Auto-generated struct predicates.** Opt-in: for `struct s { ... }`, emit a
   precise predicate `s_(p; ...fields)` = all field points-to + `malloc_block_s`.
   Removes pain #2 and gives precise predicates *for free* (feeding #1). LLMs
   then reference a standard name instead of inventing one.
2. **Lean into precise predicates as the default style.** Document
   "precise-predicate-first"; provide a lint/hint when a non-precise predicate
   forces manual open/close that a `;` would remove. Cuts pain #1 the most with
   zero core risk.
3. **Populate quick-fixes/help-topics for the top ~10 errors.** "No matching
   chunk P(...)" → QuickFix *insert `//@ open P(...);`* (or close); "leaks chunk
   P" → *insert `//@ leak`/free*; "callee not precise" → help link. Directly
   closes the LLM self-correction loop, using infra that already exists.
4. **Contract sugar**: `//@ trivial;` (= `requires true; ensures true;`) and a
   frame shorthand for read-only chunks.

### Phase 2 — the LLM verification loop (the real production enabler)
Build a driver (mirroring the weak-memory `check.sh`/`PROMPT.md` pipeline):
`verifast -json` → parse `error + help_topic + quick_fixes` → feed back to the
LLM with the failing context → LLM edits annotations → re-run, to a fixpoint or
budget. With Phase-1 quick-fixes, most iterations become "apply the suggested
open/close/lemma." This is what turns "LLM writes annotations" from a one-shot
gamble into a converging loop. A `PROMPT.md` encodes the annotation conventions
(precise predicates, the standard struct-predicate names, contract idioms).

### Phase 3 — inference (reduce what must be written at all)
- Loop-invariant heuristics / templates (frame the precise predicates of
  in-scope objects; LLM proposes the data part).
- Lightweight frame inference for calls (auto-frame the chunks a callee doesn't
  mention) — narrows the open/close gap further.
- (Stretch) bi-abduction-style pre/post suggestion for leaf functions.

### Phase 4 — a vetted kernel spec library
LLMs are far more reliable *reusing* correct predicates than inventing them.
Ship a reviewed library of kernel-shaped predicates/lemmas: intrusive lists
(`list_head`), refcounts (`kref`), RCU-protected pointers, locks, per-CPU,
bitmaps — so the LLM composes vetted building blocks. This also concentrates the
hard higher-order/concurrency reasoning (pain #7) in expert-written, reused code.

## LLM-specific guidance (why this ordering)

LLMs are good at *pattern-matching* annotations from nearby examples and a spec
library, and bad at (a) the exact `open`/`close` + ghost-arithmetic bookkeeping
and (b) inventing sound predicates from scratch. So the highest-leverage moves
are precisely: **(1) auto-open/close + auto struct predicates** to delete the
error-prone mechanical part, **(2) a vetted predicate library** to reuse, and
**(3) the `-json`/quick-fix feedback loop** so the model self-corrects from
actionable messages. Inference (Phase 3) helps but is secondary to removing the
mechanical ceremony and tightening the loop.

## Bottom line

The verbosity is real (~30%), but most of it is *mechanical* (open/close, struct
predicates) and is addressable with existing mechanisms (precise predicates,
quick-fix infra, `-json`) plus modest new code — not a research problem. The
production-grade unlock for the LLM workflow is **Phase 1 + Phase 2**:
auto-open/close-friendly defaults and auto struct predicates, then the
JSON-driven self-correcting annotation loop. Phase 4 (a kernel spec library) is
what makes it scale to real subsystems.
