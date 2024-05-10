// Justus Fasse and Bart Jacobs. Expressive modular deadlock-freedom verification. 2023.

#ifndef FUTEX_H
#define FUTEX_H

#include "atomics.h"
//@ #include <listex.gh>

/*@

lemma void call_perm_top_weaken(void *f);
    requires call_perm_top();
    ensures call_perm_(currentThread, f);

lemma void call_perm__transfer(); // This lemma is sound in the absence of busy waiting.
    requires call_perm_(_, ?f);
    ensures call_perm_(currentThread, f);

predicate call_perms_(int n, void *f) =
    n == 0 ?
        true
    :
        call_perm_(_, f) &*& call_perms_(n - 1, f);

lemma void call_below_perm__weaken(int n, void *f);
    requires call_below_perm_(_, ?f0) &*& 0 <= n &*& func_lt(f, f0) == true;
    ensures call_perms_(n, f);

fixpoint int min(int x, int y) { return x <= y ? x : y; }

fixpoint bool lex0_lt(int max_length, list<int> l1, list<int> l2) {
  switch (l1) {
    case nil: return max_length > 0 && l2 != nil;
    case cons(h1, t1): return max_length > 0 &&
      switch (l2) {
        case nil: return false;
        case cons(h2, t2): return
          0 < h2 && h1 < h2 || h1 == h2 && lex0_lt(max_length - 1, t1, t2);
    };
  }
}

lemma void lex0_lt_trans(int max_length, list<int> l1, list<int> l2, list<int> l3)
    requires lex0_lt(max_length, l1, l2) && lex0_lt(max_length, l2, l3);
    ensures lex0_lt(max_length, l1, l3) == true;
{
    switch (l1) {
        case nil:
            assert l2 == cons(_, _);
            assert l3 == cons(_, _);
        case cons(h1, t1):
            assert l2 == cons(?h2, ?t2);
            assert l3 == cons(?h3, ?t3);
            if (0 < h2 && h1 < h2) {
            } else {
                assert h1 == h2 && lex0_lt(max_length - 1, t1, t2);
                if (0 < h3 && h2 < h3) {
                } else {
                    lex0_lt_trans(max_length - 1, t1, t2, t3);
                }
            }
    }
}

lemma void lex0_lt_nonpos_max_length(int max_length, list<int> l1, list<int> l2)
    requires max_length <= 0;
    ensures !lex0_lt(max_length, l1, l2);
{
    switch (l1) {
        case nil:
        case cons(h1, t1):
            switch (l2) {
                case nil:
                case cons(h2, t2):
                    lex0_lt_nonpos_max_length(max_length - 1, t1, t2);
            }
    }
}

lemma void lex0_lt_append(int max_length, list<int> l, list<int> l1, list<int> l2)
    requires true;
    ensures lex0_lt(max_length, append(l, l1), append(l, l2)) == lex0_lt(max_length - length(l), l1, l2);
{
    switch (l) {
        case nil:
        case cons(h, t):
            if (max_length <= 0)
                lex0_lt_nonpos_max_length(max_length - length(l), l1, l2);
            else
                lex0_lt_append(max_length - 1, t, l1, l2);
    }
}

fixpoint bool lex0_subspace_lt(list<int> l1, list<int> l2) {
  switch (l1) {
    case nil: return false;
    case cons(h1, t1): return
      switch (l2) {
        case nil: return false;
        case cons(h2, t2): return
          0 < h2 && h1 < h2 || h1 == h2 && lex0_subspace_lt(t1, t2);
    };
  }
}

lemma void lex0_subspace_lt_lex0_lt(int max_length, list<int> l, list<int> l1, list<int> l2)
    requires lex0_subspace_lt(l, l2) == true && length(l) < max_length;
    ensures lex0_lt(max_length, append(l, l1), l2) == true;
{
    switch (l) {
        case nil:
        case cons(h, t):
            assert l2 == cons(?h2, ?t2);
            if (h == h2)
                lex0_subspace_lt_lex0_lt(max_length - 1, t, l1, t2);
    }
}

lemma void lex0_subspace_lt_append(list<int> l, list<int> l1, list<int> l2)
    requires lex0_subspace_lt(l1, l2) == true;
    ensures lex0_subspace_lt(append(l, l1), append(l, l2)) == true;
{
    switch (l) {
        case nil:
        case cons(h, t):
            lex0_subspace_lt_append(t, l1, l2);
    }
}

lemma void lex0_subspace_lt_append_l(list<int> l1, list<int> l, list<int> l2)
    requires lex0_subspace_lt(l1, l2) == true;
    ensures lex0_subspace_lt(append(l1, l), l2) == true;
{
    switch (l1) {
        case nil:
        case cons(h1, t1):
            assert l2 == cons(?h2, ?t2);
            if (h1 == h2) {
                lex0_subspace_lt_append_l(t1, l, t2);
            }
    }
}

fixpoint bool lex_subspace_lt(int nb_dims, list<int> l1, list<int> l2) {
    switch (l1) {
        case nil: return false;
        case cons(max_length1, l01): return
            switch (l2) {
                case nil: return false;
                case cons(max_length2, l02): return
                    max_length1 == max_length2 &&
                    length(l01) + nb_dims <= max_length1 &&
                    lex0_subspace_lt(l01, l02);
            };
    }
}

fixpoint bool lex_lt(list<int> l1, list<int> l2) {
    switch (l1) {
        case nil: return false;
        case cons(max_length1, l01): return
            switch (l2) {
                case nil: return false;
                case cons(max_length2, l02): return max_length1 == max_length2 && lex0_lt(max_length1, l01, l02);
            };
    }
}

inductive level = level(void *func, list<int> localLevel);

fixpoint bool level_lt(level l1, level l2) {
    return func_lt(l1->func, l2->func) || l1->func == l2->func && lex_lt(l1->localLevel, l2->localLevel);
}

fixpoint bool func_lt_level(void *func, level l) {
    return func_lt(func, l->func);
}

predicate obs(list<level> obs);
predicate ob(level level;);

lemma int create_ob(level level);
    requires obs(?obs);
    ensures obs(cons(level, obs)) &*& ob(level);

lemma void discharge_ob(level level);
    requires obs(?obs) &*& ob(level);
    ensures obs(remove(level, obs));

@*/

/*@

predicate futex(int *word, predicate(int nbWaiting) inv, predicate() dequeuePost, void *callPermFunc;);

// create_futex consumes the word to ensure that no two futexes, with different values for `dequeuePost` or `callPermFunc`, are active at the same word.

lemma void create_futex(int *word, predicate(int nbWaiting) inv, predicate() dequeuePost, void *callPermFunc);
    requires *word |-> ?value &*& inv(0);
    ensures futex_word(word, value) &*& futex(word, inv, dequeuePost, callPermFunc);

lemma void destroy_futex(int *word);
    requires futex_word(word, ?value) &*& futex(word, ?inv, ?dequeuePost, ?callPermFunc);
    ensures *word |-> value &*& inv(0);

@*/

/*@

typedef lemma void futex_wait_enqueue_op(int *word, predicate() P, predicate(int) Q)();
    requires [?f]futex_word(word, ?value) &*& P();
    ensures [f]futex_word(word, value) &*& Q(value);

typedef lemma void futex_wait_enqueue_ghost_op(int *word, predicate(int) inv, int val, predicate() pre, predicate(list<level>) waitInv, predicate(bool) post)();
    requires inv(?nbWaiting) &*& is_futex_wait_enqueue_op(?op, word, ?P, ?Q) &*& P() &*& pre() &*& atomic_spaces({});
    ensures
        atomic_spaces({}) &*& is_futex_wait_enqueue_op(op, word, P, Q) &*& Q(?value) &*&
        value == val ?
            obs(?obs) &*& inv(nbWaiting + 1) &*& waitInv(obs)
        :
            inv(nbWaiting) &*& post(false);

typedef lemma void futex_wait_wait_op(list<level> obs, predicate() P, predicate() Q)();
    requires [?f]ob(?level) &*& forall(obs, (level_lt)(level)) == true &*& P();
    ensures [f]ob(level) &*& Q();

typedef lemma void futex_wait_wait_ghost_op(predicate(int) inv, predicate(list<level>) waitInv)();
    requires atomic_spaces({}) &*& inv(?nbWaiting) &*& 0 < nbWaiting &*& waitInv(?obs) &*& is_futex_wait_wait_op(?op, obs, ?P, ?Q) &*& P();
    ensures atomic_spaces({}) &*& inv(nbWaiting) &*& waitInv(obs) &*& is_futex_wait_wait_op(op, obs, P, Q) &*& Q();

typedef lemma void futex_wait_dequeue_ghost_op(predicate(int) inv, predicate() dequeuePost, void *callPermFunc, predicate(list<level>) waitInv, predicate(bool) post)();
    requires atomic_spaces({}) &*& inv(?nbWaiting) &*& nbWaiting > 0 &*& waitInv(?obs) &*& obs(obs) &*& call_perm_(currentThread, callPermFunc);
    ensures atomic_spaces({}) &*& inv(nbWaiting - 1) &*& dequeuePost() &*& post(true);

@*/

void futex_wait(int *word, int val);
/*@
requires
    [?f]futex(word, ?inv, ?dequeuePost, ?callPermFunc) &*&
    is_futex_wait_enqueue_ghost_op(?eghop, word, inv, val, ?pre, ?waitInv, ?post) &*&
    is_futex_wait_wait_ghost_op(?wghop, inv, waitInv) &*&
    is_futex_wait_dequeue_ghost_op(?dghop, inv, dequeuePost, callPermFunc, waitInv, post) &*&
    pre();
@*/
//@ ensures [f]futex(word, inv, dequeuePost, callPermFunc) &*& post(?waited) &*& waited ? dequeuePost() : true;
//@ terminates;

/*@

typedef lemma void futex_wake_one_ghost_op(predicate(int) inv, predicate() dequeuePost, predicate() pre, predicate() post)();
    requires atomic_spaces({}) &*& inv(?nbWaiting) &*& (nbWaiting == 0 ? true : dequeuePost()) &*& pre();
    ensures atomic_spaces({}) &*& inv(nbWaiting) &*& (nbWaiting == 0 ? true : dequeuePost()) &*& post();

@*/

void futex_wake_one(int *word);
//@ requires [?f]futex(word, ?inv, ?dequeuePost, ?callPermFunc) &*& call_perm_(currentThread, callPermFunc) &*& is_futex_wake_one_ghost_op(?ghop, inv, dequeuePost, ?pre, ?post) &*& pre();
//@ ensures [f]futex(word, inv, dequeuePost, callPermFunc) &*& post();
//@ terminates;

/*@

typedef lemma void futex_wake_all_ghost_op(predicate(int) inv, predicate() pre, predicate() post)();
    requires atomic_spaces({}) &*& inv(0) &*& pre();
    ensures atomic_spaces({}) &*& inv(0) &*& post();

@*/

void futex_wake_all(int *word);
/*@
requires
    [?f]futex(word, ?inv, ?dequeuePost, ?callPermFunc) &*&
    call_below_perm_(currentThread, ?func) &*& func_lt(callPermFunc, func) == true &*&
    is_futex_wake_all_ghost_op(?ghop, inv, ?pre, ?post) &*& pre();
@*/
//@ ensures [f]futex(word, inv, dequeuePost, callPermFunc) &*& post();
//@ terminates;

struct thread;
typedef struct thread *thread;

//@ predicate thread(thread thread; level level, predicate() post);

typedef void thread_run_joinable/*@(level threadLevel, list<level> obs, predicate() pre, predicate() post)@*/();
//@ requires obs(cons(threadLevel, obs)) &*& pre();
//@ ensures obs({threadLevel}) &*& post();
//@ terminates;

thread fork_joinable(void *run);
//@ requires obs(?obs) &*& [_]is_thread_run_joinable(run, ?threadLevel, ?runObs, ?pre, ?post) &*& pre();
//@ ensures obs(remove_all(runObs, obs)) &*& thread(result, threadLevel, post);
//@ terminates;

void join(thread thread);
//@ requires obs(?obs) &*& thread(thread, ?level, ?post) &*& forall(obs, (level_lt)(level)) == true;
//@ ensures obs(obs) &*& post();
//@ terminates;

#endif
