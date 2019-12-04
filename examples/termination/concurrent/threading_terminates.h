#ifndef THREADING_LIVE_H
#define THREADING_LIVE_H

//@ #include "../call_perms.gh"
//@ #include "atomics.gh"
//@ #include "stop_perms.gh"

typedef void term_scope/*@(predicate(void *) pre, predicate(void *) post)@*/(void *data);
    //@ requires term_perm(?termScope, false) &*& pre(data);
    //@ ensures term_perm(termScope, false) &*& post(data);
    //@ terminates;

void call_term_scope(term_scope *scope, void *data);
    //@ requires [_]is_term_scope(scope, ?pre, ?post) &*& call_perm_(currentThread, scope) &*& pre(data);
    //@ ensures post(data);
    //@ terminates;

/*@

typedef lemma void thread_start_ghost_op(int termScope, predicate() inv, void *data, predicate(int, void *) pre, predicate(void *) forkerPost, predicate(int, void *) forkeePost)();
    requires inv() &*& pre(?callPermScope, data) &*& stop_perm(termScope);
    ensures inv() &*& forkerPost(data) &*& forkeePost(callPermScope, data);

@*/

typedef void thread_run/*@(int termScope, predicate(int callPermScope, void *data) pre)@*/(void *data);
    //@ requires pre(call_perm_scope_of(currentThread), data);
    //@ ensures stop_perm(termScope);
    //@ terminates;

void thread_start(thread_run *run, void *data);
    /*@
    requires
        [?fts]term_perm(?termScope, false) &*&
        [?f]atomic_space(?level, ?inv) &*&
        is_thread_start_ghost_op(_, termScope, inv, data, ?pre, ?forkerPost, ?forkeePost) &*&
        [_]is_thread_run(run, termScope, forkeePost) &*&
        call_perm_(currentThread, run) &*&
        pre(call_perm_scope_of(currentThread), data);
    @*/
    //@ ensures [fts]term_perm(termScope, false) &*& [f]atomic_space(level, inv) &*& forkerPost(data);
    //@ terminates;

struct semaphore;
typedef struct semaphore *semaphore;

/*@

predicate semaphore(semaphore s, int items, int blockees);

typedef lemma void semaphore_sep(real level, predicate() inv, semaphore s, predicate() sep, predicate(int, int) unsep)();
    requires atomic_space_level(level) &*& inv() &*& sep();
    ensures atomic_space_level(level) &*& semaphore(s, ?items, ?blockees) &*& unsep(items, blockees);

typedef lemma void semaphore_unsep(real level, predicate() inv, semaphore s, predicate() sep, predicate(int, int) unsep)();
    requires atomic_space_level(level) &*& semaphore(s, ?items, ?blockees) &*& unsep(items, blockees);
    ensures atomic_space_level(level) &*& inv() &*& sep();

typedef lemma void semaphore_acquire_block(int termScope, real level, predicate(int, int) unsep, predicate() P, predicate() blocked)();
    requires atomic_space_level(level) &*& unsep(0, ?blockees) &*& P();
    ensures atomic_space_level(level) &*& unsep(0, blockees + 1) &*& blocked() &*& stop_perm(termScope);

typedef lemma void semaphore_acquire_unblock(int termScope, real level, predicate(int, int) unsep, predicate() blocked, predicate() P)();
    requires atomic_space_level(level) &*& unsep(0, ?blockees) &*& blockees > 0 &*& blocked() &*& stop_perm(termScope);
    ensures atomic_space_level(level) &*& unsep(0, blockees - 1) &*& P();

typedef lemma void semaphore_acquire_success(real level, predicate(int, int) unsep, predicate() P, predicate() Q)();
    requires atomic_space_level(level) &*& unsep(?items, 0) &*& items > 0 &*& P();
    ensures atomic_space_level(level) &*& unsep(items - 1, 0) &*& Q();

typedef lemma void semaphore_release(real level, predicate() inv, semaphore s, predicate(int, int) unsep, real frac, predicate() P, predicate() Q)();
    requires atomic_space_level(level) &*& semaphore(s, ?items, 0) &*& unsep(items - 1, 0) &*& P() &*& [frac]atomic_space(level, inv);
    ensures atomic_space_level(level) &*& inv() &*& Q();

typedef lemma void inv_has_term_perm(int termScope, predicate() inv)();
    requires inv() &*& [_]term_perm(termScope, true);
    ensures false;

@*/

semaphore create_semaphore(int items);
    //@ requires 0 <= items;
    //@ ensures semaphore(result, items, 0);
    //@ terminates;

void semaphore_acquire(semaphore s);
    /*@
    requires
        exists<real>(?level) &*&
        [?f]atomic_space(level, ?inv) &*& [_]is_inv_has_term_perm(_, ?termScope, inv) &*&
        is_semaphore_sep(_, level, inv, s, ?sep, ?unsep) &*&
        is_semaphore_unsep(_, level, inv, s, sep, unsep) &*&
        is_semaphore_acquire_block(_, termScope, level, unsep, ?P, ?blocked) &*&
        is_semaphore_acquire_unblock(_, termScope, level, unsep, blocked, P) &*&
        is_semaphore_acquire_success(_, level, unsep, P, ?Q) &*&
        sep() &*& P();
    @*/
    //@ ensures [f]atomic_space(level, inv) &*& sep() &*& Q();
    //@ terminates;

void semaphore_release(semaphore s);
    /*@
    requires
        [?f]atomic_space(?level, ?inv) &*& [_]is_inv_has_term_perm(_, ?termScope, inv) &*&
        is_semaphore_sep(_, level, inv, s, ?sep, ?unsep) &*&
        is_semaphore_unsep(_, level, inv, s, sep, unsep) &*&
        is_semaphore_release(_, level, inv, s, unsep, f, ?P, ?Q) &*&
        sep() &*& P();
    @*/
    //@ ensures Q();
    //@ terminates;

void semaphore_dispose(semaphore s);
    //@ requires semaphore(s, ?items, ?blockees);
    //@ ensures blockees == 0;
    //@ terminates;

/*@

typedef lemma void *atomic_load_op(void **pp, predicate() pre, predicate(void *) post)();
    requires pre() &*& [?f]pointer(pp, ?p);
    ensures post(p) &*& [f]pointer(pp, p) &*& result == p;

typedef lemma void atomic_load_ctxt(real level, predicate() inv, void **pp, predicate() P, predicate(void *) Q)();
    requires atomic_space_level(level) &*& inv() &*& P() &*& is_atomic_load_op(?op, pp, ?pre, ?post) &*& pre();
    ensures atomic_space_level(level) &*& inv() &*& post(?p) &*& Q(p) &*& is_atomic_load_op(op, pp, pre, post);

@*/

void *atomic_load(void **pp);
    //@ requires [?f]atomic_space(?level, ?inv) &*& is_atomic_load_ctxt(?ctxt, level, inv, pp, ?P, ?Q) &*& P();
    //@ ensures [f]atomic_space(level, inv) &*& Q(result);
    //@ terminates;

/*@

typedef lemma void *atomic_compare_and_swap_op(void **pp, void *old, void *new, predicate() pre, predicate(void *) post)();
    requires pre() &*& [?f]pointer(pp, ?p) &*& p == old ? f == 1 : true;
    ensures post(p) &*& [f]pointer(pp, p == old ? new : p);

typedef lemma void atomic_compare_and_swap_ctxt(real level, predicate() inv, void **pp, void *old, void *new, predicate() P, predicate(void *) Q)();
    requires atomic_space_level(level) &*& inv() &*& P() &*& is_atomic_compare_and_swap_op(?op, pp, old, new, ?pre, ?post) &*& pre();
    ensures atomic_space_level(level) &*& inv() &*& post(?p) &*& Q(p) &*& is_atomic_compare_and_swap_op(op, pp, old, new, pre, post);

@*/

void *atomic_compare_and_swap(void **pp, void *old, void *new);
    //@ requires [?f]atomic_space(?level, ?inv) &*& is_atomic_compare_and_swap_ctxt(?ctxt, level, inv, pp, old, new, ?P, ?Q) &*& P();
    //@ ensures [f]atomic_space(level, inv) &*& Q(result);
    //@ terminates;

/*@

typedef lemma void atomic_store_op(void **pp, void *p, predicate() pre, predicate() post)();
    requires pre() &*& pointer(pp, _);
    ensures post() &*& pointer(pp, p);

typedef lemma void atomic_store_ctxt(real level, predicate() inv, void **pp, void *p, predicate() P, predicate() Q, real f)();
    requires atomic_space_level(level) &*& inv() &*& P() &*& is_atomic_store_op(?op, pp, p, ?pre, ?post) &*& pre() &*& [f]atomic_space(level, inv);
    ensures atomic_space_level(level) &*& inv() &*& Q() &*& is_atomic_store_op(op, pp, p, pre, post) &*& post();

@*/

void atomic_store(void **pp, void *p);
    //@ requires [?f]atomic_space(?level, ?inv) &*& is_atomic_store_ctxt(?ctxt, level, inv, pp, p, ?P, ?Q, f) &*& P() &*& is_inv_has_term_perm(_, _, inv);
    //@ ensures is_atomic_store_ctxt(ctxt, level, inv, pp, p, P, Q, f) &*& Q();
    //@ terminates;

#endif
