#ifndef FUTEX_H
#define FUTEX_H

/*@

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

predicate obs(list<pair<int, level> > obs);
predicate ob(int id; level level, bool discharged);

lemma int create_ob(level level);
    requires obs(?obs);
    ensures obs(cons(pair(result, level), obs)) &*& ob(result, level, false);

lemma void discharge_ob(int id);
    requires obs(?obs) &*& ob(id, ?level, false) &*& mem(pair(id, level), obs) == true;
    ensures obs(remove(pair(id, level), obs)) &*& ob(id, level, true);

@*/

/*@

predicate futex(int *word; predicate(int, int, int) inv);

lemma void init_futex(int *word, predicate(int, int, int) inv);
    requires *word |-> ?value &*& inv(value, 0, 0);
    ensures futex(word, inv);

lemma void destroy_futex(int *word);
    requires futex(word, ?inv);
    ensures *word |-> ?value &*& inv(value, 0, 0);

@*/

/*@

typedef lemma void futex_wait_mismatch_ghost_op(predicate(int, int, int) inv, int val, predicate() pre, predicate() post)();
    requires inv(?actualVal, ?nbWaiting, nbWaiting) &*& actualVal != val &*& pre();
    ensures inv(actualVal, nbWaiting, nbWaiting) &*& post();

typedef lemma void futex_wait_enqueue_ghost_op(predicate(int, int, int) inv, int val, predicate() pre, predicate() waitInv)();
    requires inv(val, ?nbWaiting, nbWaiting) &*& pre();
    ensures inv(val, nbWaiting + 1, nbWaiting + 1) &*& waitInv();

typedef lemma void futex_wait_wait_op(list<pair<int, level> > obs, predicate() P, predicate() Q)(int id);
    requires ob(id, ?level, false) &*& forall(map(snd, obs), (level_lt)(level)) == true &*& P();
    ensures ob(id, level, false) &*& Q();

typedef lemma void futex_wait_wait_ghost_op(predicate(int, int, int) inv, list<pair<int, level> > obs, predicate() waitInv)();
    requires inv(?val, ?nbWaiting, nbWaiting) &*& is_futex_wait_wait_op(?op, obs, ?P, ?Q) &*& P() &*& waitInv();
    ensures inv(val, nbWaiting, nbWaiting) &*& is_futex_wait_wait_op(op, obs, P, Q) &*& Q() &*& waitInv();

typedef lemma void futex_wait_dequeue_ghost_op(predicate(int, int, int) inv, predicate() waitInv, predicate() post)();
    requires inv(?val, ?nbWaiting, ?nbShouldBeWaiting) &*& nbShouldBeWaiting < nbWaiting &*& waitInv();
    ensures inv(val, nbWaiting - 1, nbShouldBeWaiting) &*& post();

@*/

void futex_wait(int *word, int val);
/*@
requires
    obs(?obs) &*& [?f]futex(word, ?inv) &*&
    is_futex_wait_mismatch_ghost_op(?mghop, inv, val, ?pre, ?post) &*&
    is_futex_wait_enqueue_ghost_op(?eghop, inv, val, pre, ?waitInv) &*&
    is_futex_wait_wait_ghost_op(?wghop, inv, obs, waitInv) &*&
    is_futex_wait_dequeue_ghost_op(?dghop, inv, waitInv, post) &*&
    pre();
@*/
//@ ensures obs(obs) &*& [f]futex(word, inv) &*& post();

/*@

fixpoint int min(int x, int y) { return x <= y ? x : y; }

typedef lemma void futex_wake_ghost_op(predicate(int, int, int) inv, int count, predicate() pre, predicate() post)();
    requires inv(?val, ?nbWaiting, nbWaiting) &*& pre();
    ensures inv(val, nbWaiting, nbWaiting - min(nbWaiting, count)) &*& post();

@*/

void futex_wake(int *word, int count);
//@ requires [?f]futex(word, ?inv) &*& 0 <= count &*& is_futex_wake_ghost_op(?ghop, inv, count, ?pre, ?post) &*& pre();
//@ ensures [f]futex(word, inv) &*& post();

#endif
