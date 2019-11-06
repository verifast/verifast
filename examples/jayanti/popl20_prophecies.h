#ifndef POPL20_PROPHECIES_H
#define POPL20_PROPHECIES_H

/*

This header file provides one possible axiomatization into VeriFast of the prophecy variables construct proposed in

    Ralf Jung, Rodolphe Lepigre, Gaurav Parthasarathy, Marianna Rapoport, Amin Timany, Derek Dryer, and Bart Jacobs. The Future is Ours: Prophecy Variables in Separation Logic. In Proc. POPL 2020.

Differences with the paper:

The programming language of the paper:
- is untyped
- has a rich notion of pure values, including unbounded integers and pairs
- has a "Resolve" construct that wraps an atomic command

In contrast, in this axiomatisation:
- 64-bit numbers are used as prophecy variable identifiers. This means this axiomatisation is sound only for (partial) runs where the program allocates fewer than 2^64 prophecy variables.
- Resolution is built into the various atomic commands.
- Only scalar values are supported as marker values.

*/

typedef long long popl20_prophecy_id;

/*@

predicate popl20_prophecy(popl20_prophecy_id pid, list<pair<int, list<vararg> > > vs);

lemma void popl20_prophecy_inv(popl20_prophecy_id pid);
    requires popl20_prophecy(pid, ?vs);
    ensures popl20_prophecy(pid, vs) &*& pid != 0;

@*/

popl20_prophecy_id create_popl20_prophecy();
//@ requires true;
//@ ensures popl20_prophecy(result, _) &*& result != 0;

/*@

// An 'atomic space' is a VeriFast equivalent/approximation of an Iris 'invariant' or a CAP/TaDA 'shared region'

predicate popl20_atomic_space(void *name, predicate() inv;);
predicate popl20_atomic_spaces(list<pair<void *, predicate()> > openedSpaces);

lemma void create_popl20_atomic_space(void *name, predicate() inv);
    requires inv();
    ensures popl20_atomic_space(name, inv);

lemma void dispose_popl20_atomic_space();
    nonghost_callers_only
    requires popl20_atomic_space(?name, ?inv);
    ensures inv();

typedef lemma void popl20_atomic_noop_ctxt(predicate() pre, predicate() post)();
    requires popl20_atomic_spaces(nil) &*& pre();
    ensures popl20_atomic_spaces(nil) &*& post();

lemma void popl20_atomic_noop();
    nonghost_callers_only // This ensures you cannot call it from inside another atomic operation, i.e. in Iris terms, this ensures the mask is Top.
    requires is_popl20_atomic_noop_ctxt(?ctxt, ?pre, ?post) &*& pre();
    ensures post();

lemma void popl20_open_atomic_space();
    requires popl20_atomic_spaces(?openedSpaces) &*& [?f]popl20_atomic_space(?name, ?inv) &*& !mem(pair(name, inv), openedSpaces);
    ensures popl20_atomic_spaces(cons(pair(name, inv), openedSpaces)) &*& [f]popl20_atomic_space(name, inv) &*& inv();

lemma void popl20_close_atomic_space();
    requires popl20_atomic_spaces(?openedSpaces) &*& [?f]popl20_atomic_space(?name, ?inv) &*& mem(pair(name, inv), openedSpaces) == true &*& inv();
    ensures popl20_atomic_spaces(remove(pair(name, inv), openedSpaces)) &*& [f]popl20_atomic_space(name, inv);

@*/

typedef long long resolve_list_id;

//@ inductive resolve_cmd = resolve_cmd(popl20_prophecy_id pid, list<vararg> marker);

//@ predicate resolve_list(resolve_list_id rlid, list<resolve_cmd> resolveCmds);

resolve_list_id create_resolve_list();
//@ requires true;
//@ ensures resolve_list(result, nil);

void resolve_list_push(resolve_list_id rlid, popl20_prophecy_id pid, ...);
//@ requires resolve_list(rlid, ?resolveCmds);
//@ ensures resolve_list(rlid, cons(resolve_cmd(pid, varargs), resolveCmds));

/*@

predicate prophecies(list<resolve_cmd> resolveCmds, list<list<pair<int, list<vararg> > > > vss) =
    switch (resolveCmds) {
    case nil: return vss == nil;
    case cons(resolveCmd, resolveCmds0): return
        resolveCmd == resolve_cmd(?pid, ?marker) &*&
        vss == cons(?vs0, ?vss0) &*&
        popl20_prophecy(pid, vs0) &*&
        prophecies(resolveCmds0, vss0);
    };

predicate prophecies_resolved(list<resolve_cmd> resolveCmds, list<list<pair<int, list<vararg> > > > vss, int result) =
    switch (resolveCmds) {
    case nil: return vss == nil;
    case cons(resolveCmd, resolveCmds0): return
        resolveCmd == resolve_cmd(?pid, ?marker) &*&
        vss == cons(?vs0, ?vss0) &*&
        vs0 == cons(pair(result, marker), ?vs00) &*&
        popl20_prophecy(pid, vs00) &*&
        prophecies_resolved(resolveCmds0, vss0, result);
    };

@*/

/*@

typedef lemma void popl20_atomic_load_int_ghop(int *pv, list<resolve_cmd> resolveCmds, predicate() P, predicate(int) Q)();
    requires [?f]*pv |-> ?v &*& prophecies(resolveCmds, ?vss) &*& P();
    ensures [f]*pv |-> v &*& prophecies_resolved(resolveCmds, vss, v) &*& Q(v);

typedef lemma void popl20_atomic_load_int_ctxt(int *pv, list<resolve_cmd> resolveCmds, predicate() pre, predicate(int) post)();
    requires popl20_atomic_spaces(nil) &*& pre() &*& is_popl20_atomic_load_int_ghop(?ghop, pv, resolveCmds, ?P, ?Q) &*& P();
    ensures popl20_atomic_spaces(nil) &*& is_popl20_atomic_load_int_ghop(ghop, pv, resolveCmds, P, Q) &*& Q(?result) &*& post(result);

@*/

int popl20_atomic_load_int(int *pv, resolve_list_id rlid);
/*@
requires
    resolve_list(rlid, ?resolveCmds) &*&
    is_popl20_atomic_load_int_ctxt(?ctxt, pv, resolveCmds, ?pre, ?post) &*& pre();
@*/
/*@
ensures
    resolve_list(rlid, nil) &*&
    post(result);
@*/

/*@

typedef lemma void popl20_atomic_load_pointer_ghop(void **pp, list<resolve_cmd> resolveCmds, predicate() P, predicate(void *) Q)();
    requires [?f]*pp |-> ?p &*& prophecies(resolveCmds, ?vss) &*& P();
    ensures [f]*pp |-> p &*& prophecies_resolved(resolveCmds, vss, (uintptr_t)p) &*& Q(p);

typedef lemma void popl20_atomic_load_pointer_ctxt(void **pp, list<resolve_cmd> resolveCmds, predicate() pre, predicate(void *) post)();
    requires popl20_atomic_spaces(nil) &*& pre() &*& is_popl20_atomic_load_pointer_ghop(?ghop, pp, resolveCmds, ?P, ?Q) &*& P();
    ensures popl20_atomic_spaces(nil) &*& is_popl20_atomic_load_pointer_ghop(ghop, pp, resolveCmds, P, Q) &*& Q(?result) &*& post(result);

@*/

void *popl20_atomic_load_pointer(void **pp, resolve_list_id rlid);
/*@
requires
    resolve_list(rlid, ?resolveCmds) &*&
    is_popl20_atomic_load_pointer_ctxt(?ctxt, pp, resolveCmds, ?pre, ?post) &*& pre();
@*/
/*@
ensures
    resolve_list(rlid, nil) &*&
    post(result);
@*/

/*@

fixpoint bool fst_head_eq<a, b>(a x, list<pair<a, b> > xys) {
    switch (xys) {
    case nil: return false;
    case cons(xy0, xys0): return fst(xy0) == x;
    }
}

typedef lemma void popl20_atomic_store_int_ghop(int *pv, int v, list<resolve_cmd> resolveCmds, predicate() P, predicate() Q)();
    requires [?f]*pv |-> ?v0 &*& prophecies(resolveCmds, ?vss) &*& P() &*& !forall(vss, (fst_head_eq)(v0)) || f == 1;
    ensures [f]*pv |-> v &*& prophecies_resolved(resolveCmds, vss, v0) &*& Q();

typedef lemma void popl20_atomic_store_int_ctxt(int *pv, int v, list<resolve_cmd> resolveCmds, predicate() pre, predicate() post)();
    requires popl20_atomic_spaces(nil) &*& is_popl20_atomic_store_int_ghop(?ghop, pv, v, resolveCmds, ?P, ?Q) &*& P() &*& pre();
    ensures popl20_atomic_spaces(nil) &*& is_popl20_atomic_store_int_ghop(ghop, pv, v, resolveCmds, P, Q) &*& Q() &*& post();

@*/

void popl20_atomic_store_int(int *pv, int v, resolve_list_id rlid);
/*@
requires
    resolve_list(rlid, ?resolveCmds) &*&
    is_popl20_atomic_store_int_ctxt(?ctxt, pv, v, resolveCmds, ?pre, ?post) &*& pre();
@*/
/*@
ensures
    resolve_list(rlid, nil) &*&
    post();
@*/

/*@

typedef lemma void popl20_atomic_compare_and_swap_pointer_ghop(void **pp, void *old, void *new, list<resolve_cmd> resolveCmds, predicate() P, predicate(void *) Q)();
    requires [?f]*pp |-> ?p &*& prophecies(resolveCmds, ?vss) &*& P() &*& p != old || !forall(vss, (fst_head_eq)((uintptr_t)p)) || f == 1;
    ensures [f]*pp |-> (p == old ? new : p) &*& prophecies_resolved(resolveCmds, vss, (uintptr_t)p) &*& Q(p);

typedef lemma void popl20_atomic_compare_and_swap_pointer_ctxt(void **pp, void *old, void *new, list<resolve_cmd> resolveCmds, predicate() pre, predicate(void *) post)();
    requires popl20_atomic_spaces(nil) &*& is_popl20_atomic_compare_and_swap_pointer_ghop(?ghop, pp, old, new, resolveCmds, ?P, ?Q) &*& P() &*& pre();
    ensures popl20_atomic_spaces(nil) &*& is_popl20_atomic_compare_and_swap_pointer_ghop(ghop, pp, old, new, resolveCmds, P, Q) &*& Q(?result) &*& post(result);

@*/

void *popl20_atomic_compare_and_swap_pointer(void **pp, void *old, void *new, resolve_list_id rlid);
/*@
requires
    resolve_list(rlid, ?resolveCmds) &*&
    is_popl20_atomic_compare_and_swap_pointer_ctxt(?ctxt, pp, old, new, resolveCmds, ?pre, ?post) &*& pre();
@*/
/*@
ensures
    resolve_list(rlid, nil) &*&
    post(result);
@*/

#endif