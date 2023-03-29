// Tobias Reinhard and Bart Jacobs. Ghost signals: verifying termination of busy-waiting. 2020.

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

fixpoint bool level0_lt(int max_length, list<int> l1, list<int> l2) {
  switch (l1) {
    case nil: return max_length > 0 && l2 != nil;
    case cons(h1, t1): return max_length > 0 &&
      switch (l2) {
        case nil: return false;
        case cons(h2, t2): return
          0 < h2 && h1 < h2 || h1 == h2 && level0_lt(max_length - 1, t1, t2);
    };
  }
}

lemma void level0_lt_nonpos_max_length(int max_length, list<int> l1, list<int> l2)
    requires max_length <= 0;
    ensures !level0_lt(max_length, l1, l2);
{
    switch (l1) {
        case nil:
        case cons(h1, t1):
            switch (l2) {
                case nil:
                case cons(h2, t2):
                    level0_lt_nonpos_max_length(max_length - 1, t1, t2);
            }
    }
}

lemma void level0_lt_append(int max_length, list<int> l, list<int> l1, list<int> l2)
    requires true;
    ensures level0_lt(max_length, append(l, l1), append(l, l2)) == level0_lt(max_length - length(l), l1, l2);
{
    switch (l) {
        case nil:
        case cons(h, t):
            if (max_length <= 0)
                level0_lt_nonpos_max_length(max_length - length(l), l1, l2);
            else
                level0_lt_append(max_length - 1, t, l1, l2);
    }
}

fixpoint bool all_sublevel0s_lt(list<int> l1, list<int> l2) {
  switch (l1) {
    case nil: return false;
    case cons(h1, t1): return
      switch (l2) {
        case nil: return false;
        case cons(h2, t2): return
          0 < h2 && h1 < h2 || h1 == h2 && all_sublevel0s_lt(t1, t2);
    };
  }
}

lemma void all_sublevel0s_lt_append(int max_length, list<int> l, list<int> l1, list<int> l2)
    requires all_sublevel0s_lt(l, l2) == true && length(l) < max_length;
    ensures level0_lt(max_length, append(l, l1), l2) == true;
{
    switch (l) {
        case nil:
        case cons(h, t):
            assert l2 == cons(?h2, ?t2);
            if (h == h2)
                all_sublevel0s_lt_append(max_length - 1, t, l1, t2);
    }
}

fixpoint bool all_sublevels_lt(int nb_dims, list<int> l1, list<int> l2) {
    switch (l1) {
        case nil: return false;
        case cons(max_length1, l01): return
            switch (l2) {
                case nil: return false;
                case cons(max_length2, l02): return
                    max_length1 == max_length2 &&
                    length(l01) + nb_dims <= max_length1 &&
                    all_sublevel0s_lt(l01, l02);
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

fixpoint bool level_lt(list<int> l1, list<int> l2) {
    switch (l1) {
        case nil: return false;
        case cons(max_length1, l01): return
            switch (l2) {
                case nil: return false;
                case cons(max_length2, l02): return max_length1 == max_length2 && level0_lt(max_length1, l01, l02);
            };
    }
}

@*/

//@ predicate obs(list<pathcomp> path, list<pair<void *, list<int> > > obs);

//@ fixpoint list<int> level_of(pair<void *, list<int> > ob) { return snd(ob); }

/*@

predicate call_below_perm(list<pathcomp> path, void *f;);

predicate call_below_perms(int n, list<pathcomp> path, void *f;) =
    n <= 0 ?
        true
    :
        call_below_perm(path, f) &*& call_below_perms(n - 1, path, f);

lemma void pathize_call_below_perm_();
  requires obs(?p, ?obs) &*& call_below_perm_(currentThread, ?f);
  ensures obs(p, obs) &*& call_below_perm(p, f);

lemma void pathize_call_below_perm__multi(int n);
  requires obs(?p, ?obs) &*& call_below_perm_(currentThread, ?f);
  ensures obs(p, obs) &*& call_below_perms(n, p, f);

fixpoint bool lt(int x, int y) { return x < y; }

fixpoint bool le(int x, int y) { return x <= y; }

@*/

typedef void thread_run/*@(list<pathcomp> path, list<pair<void *, list<int> > > obs, predicate() pre)@*/();
//@ requires obs(cons(Forkee, path), obs) &*& pre();
//@ ensures obs(_, nil);
//@ terminates;

void fork(thread_run *run);
//@ requires obs(?p, ?obs) &*& [_]is_thread_run(run, p, ?forkee_obs, ?pre) &*& pre();
//@ ensures obs(cons(Forker, p), remove_all(forkee_obs, obs));
//@ terminates;

/*@

predicate signal_uninit(void *id;);

lemma void *create_signal();
  requires true;
  ensures signal_uninit(result);

predicate signal(void *id; list<int> level, bool status);

lemma void init_signal(void *signal, list<int> level);
  requires obs(?p, ?obs) &*& signal_uninit(signal);
  ensures obs(p, cons(pair(signal, level), obs)) &*& signal(signal, level, false);

lemma void set_signal(void *signal);
  requires obs(?p, ?obs) &*& signal(signal, ?level, false);
  ensures obs(p, remove(pair(signal, level), obs)) &*& signal(signal, level, true);

predicate wait_perm(list<pathcomp> path, void *signal, list<int> level, void *func;);

lemma void create_wait_perm(void *s, list<int> level, void *f);
  requires call_below_perm(?p, ?f0) &*& func_lt(f, f0) == true;
  ensures wait_perm(p, s, level, f);

lemma void wait(void *s);
  requires
    obs(?p, ?obs) &*& wait_perm(?pp, s, ?level, ?f) &*&
    signal(s, level, false) &*&
    is_ancestor_of(pp, p) == true &*&
    forall(map(snd, obs), (level_lt)(level)) == true;
  ensures
    obs(p, obs) &*& wait_perm(pp, s, level, f) &*&
    signal(s, level, false) &*&
    call_perm_(currentThread, f);

@*/

#endif
