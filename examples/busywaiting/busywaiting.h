// Tobias Reinhard and Bart Jacobs. Ghost signals: verifying termination of busy-waiting. 2020.
// Justus Fasse and Bart Jacobs. Expressive modular verification of termination for busy-waiting programs. 2023.

#ifndef BUSYWAITING_H
#define BUSYWAITING_H

//@ #include <listex.gh>

//@ inductive pathcomp = Forker | Forkee;

/*@

fixpoint bool is_ancestor_of(list<pathcomp> p1, list<pathcomp> p2) {
  switch (p2) {
    case nil: return p1 == nil;
    case cons(p2h, p2t): return p1 == p2 || is_ancestor_of(p1, p2t);
  }
}

lemma void is_ancestor_of_refl(list<pathcomp> p)
    requires true;
    ensures is_ancestor_of(p, p) == true;
{
    switch (p) { case nil: case cons(h, t): }
}

lemma void is_ancestor_of_trans(list<pathcomp> p1, list<pathcomp> p2, list<pathcomp> p3)
    requires is_ancestor_of(p1, p2) && is_ancestor_of(p2, p3);
    ensures is_ancestor_of(p1, p3) == true;
{
    switch (p3) {
        case nil:
        case cons(p3h, p3t):
            if (p2 == p3) {
            } else {
                is_ancestor_of_trans(p1, p2, p3t);
            }
    }
}

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

fixpoint bool is_prefix_of<t>(list<t> xs, list<t> ys) {
    switch (xs) {
        case nil: return true;
        case cons(hxs, txs): return
            switch (ys) {
                case nil: return false;
                case cons(hys, tys): return hxs == hys && is_prefix_of(txs, tys);
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

@*/

//@ inductive level = level(void *func, list<int> localLevel);

//@ predicate obs_(int thread, list<pathcomp> path, list<pair<void *, level> > obs);

/*@

#define obs(p, obs) obs_(currentThread, p, obs)

@*/

//@ fixpoint level level_of(pair<void *, level> ob) { return snd(ob); }

/*@

predicate call_below_perm(list<pathcomp> path, void *f;);

predicate call_below_perms(int n, list<pathcomp> path, void *f;) =
    n <= 0 ?
        true
    :
        call_below_perm(path, f) &*& call_below_perms(n - 1, path, f);

lemma void call_below_perms_weaken(int m)
    requires call_below_perms(?n, ?p, ?f) &*& m <= n;
    ensures call_below_perms(m, p, f);
{
    open call_below_perms(_, _, _);
    if (n <= 0 || n == m)
        close call_below_perms(m, p, f);
    else {
        leak call_below_perm(_, _);
        call_below_perms_weaken(m);
    }
}

lemma void pathize_call_below_perm_();
  requires obs_(?thread, ?p, ?obs) &*& call_below_perm_(thread, ?f);
  ensures obs_(thread, p, obs) &*& call_below_perm(p, f);

lemma void pathize_call_below_perm__multi(int n);
  requires obs_(?thread, ?p, ?obs) &*& call_below_perm_(thread, ?f);
  ensures obs_(thread, p, obs) &*& call_below_perms(n, p, f);

fixpoint bool lt(int x, int y) { return x < y; }

fixpoint bool le(int x, int y) { return x <= y; }

@*/

typedef void thread_run/*@(list<pathcomp> path, list<pair<void *, level> > obs, predicate() pre)@*/();
//@ requires obs(cons(Forkee, path), obs) &*& pre();
//@ ensures obs(_, nil);
//@ terminates;

void fork(thread_run *run);
//@ requires obs(?p, ?obs) &*& [_]is_thread_run(run, p, ?forkee_obs, ?pre) &*& length(remove_all(forkee_obs, obs)) == length(obs) - length(forkee_obs) &*& pre();
//@ ensures obs(cons(Forker, p), remove_all(forkee_obs, obs));
//@ terminates;

typedef void thread_run_joinable/*@(list<pathcomp> path, list<pair<void *, level> > obs, predicate() pre, predicate() post, level level)@*/();
//@ requires obs(cons(Forkee, path), cons(pair(?terminationSignal, level), obs)) &*& pre();
//@ ensures obs(_, {pair(terminationSignal, level)}) &*& post();

struct thread;
typedef struct thread *thread;

//@ predicate thread(thread thread, level level, predicate() post);

thread fork_joinable(thread_run_joinable *run);
//@ requires obs(?p, ?obs) &*& [_]is_thread_run_joinable(run, p, ?forkee_obs, ?pre, ?post, ?level) &*& length(remove_all(forkee_obs, obs)) == length(obs) - length(forkee_obs) &*& pre();
//@ ensures obs(cons(Forker, p), remove_all(forkee_obs, obs)) &*& thread(result, level, post);
//@ terminates;

/*@

fixpoint bool level_lt(level l1, level l2) {
    return func_lt(l1->func, l2->func) || l1->func == l2->func && lex_lt(l1->localLevel, l2->localLevel);
}

fixpoint bool all_sublevels_lt(int nbDims, level l1, level l2) {
    return func_lt(l1->func, l2->func) || l1->func == l2->func && lex_subspace_lt(nbDims, l1->localLevel, l2->localLevel);
}

fixpoint int level_subspace_nb_dims(level l) {
    return head(l->localLevel) - length(tail(l->localLevel));
}

fixpoint level sublevel(level l, list<int> ks) {
    switch (l) {
        case level(f, localLevel): return level(f, append(localLevel, ks));
    }
}

fixpoint bool func_lt_level(void *f, level l) {
    return func_lt(f, l->func);
}

@*/

void join(thread thread);
//@ requires obs(?p, ?obs) &*& thread(thread, ?level, ?post) &*& forall(map(snd, obs), (level_lt)(level)) == true;
//@ ensures obs(p, obs) &*& post();
//@ terminates;

/*@

predicate signal_uninit(void *id;);

lemma void *create_signal();
  requires true;
  ensures signal_uninit(result);

predicate signal(void *id; level level, bool status);

lemma void init_signal(void *signal, level level);
  requires obs_(?thread, ?p, ?obs) &*& signal_uninit(signal);
  ensures obs_(thread, p, cons(pair(signal, level), obs)) &*& signal(signal, level, false);

lemma void set_signal(void *signal);
  requires obs_(?thread, ?p, ?obs) &*& signal(signal, ?level, false) &*& mem(pair(signal, level), obs) == true;
  ensures obs_(thread, p, remove(pair(signal, level), obs)) &*& signal(signal, level, true);

lemma void ob_signal_not_set(void *signal);
  requires obs_(?thread, ?p, ?obs) &*& signal(signal, ?level, ?status) &*& mem(signal, map(fst, obs)) == true;
  ensures obs_(thread, p, obs) &*& signal(signal, level, status) &*& !status;

predicate wait_perm(list<pathcomp> path, void *signal, level level, void *func;);

lemma void create_wait_perm(void *s, level level, void *f);
  requires call_below_perm(?p, ?f0) &*& func_lt(f, f0) == true;
  ensures wait_perm(p, s, level, f);

lemma void wait(void *s);
  requires
    obs_(?thread, ?p, ?obs) &*& wait_perm(?pp, s, ?level, ?f) &*&
    signal(s, level, false) &*&
    is_ancestor_of(pp, p) == true &*&
    forall(map(snd, obs), (level_lt)(level)) == true;
  ensures
    obs_(thread, p, obs) &*& wait_perm(pp, s, level, f) &*&
    signal(s, level, false) &*&
    call_perm_(thread, f);

@*/

#endif
