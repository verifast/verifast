#include <stdlib.h>
#include "tso.h"

struct lock {
    //@ int tso_id;
    //@ real frac;
    void *locked; // Zero=free; Nonzero=locked
};

/*@

predicate_ctor lock_inv(struct lock *lock, predicate() inv)(unit u) =
    pointer(&lock->locked, ?v) &*&
    v == 0 ?
        lock->frac |-> _ &*& inv()
    :
        [1/2]lock->frac |-> ?f &*& [f/2]lock->tso_id |-> _;

fixpoint bool unit_le(unit u1, unit u2) { return true; }

fixpoint unit idf(list<vararg> args, unit u) { return unit; }

predicate lock(struct lock *lock, predicate() inv;) =
    lock->tso_id |-> ?id &*&
    tso(id, lock_inv(lock, inv), unit_le, cons(idf, nil), unit) &*&
    malloc_block_lock(lock);

predicate locked(struct lock *lock, predicate() inv, real f) =
    [f/2]lock->tso_id |-> ?id &*&
    [1/2]lock->frac |-> f &*&
    [f]malloc_block_lock(lock) &*&
    [f]tso(id, lock_inv(lock, inv), unit_le, cons(idf, nil), unit);

lemma void unit_le_refl(unit u)
    requires true;
    ensures unit_le(u, u) == true;
{
    switch (u) { case unit: }
}

lemma void unit_le_trans(unit u1, unit u2, unit u3)
    requires unit_le(u1, u2) == true &*& unit_le(u2, u3) == true;
    ensures unit_le(u1, u3) == true;
{
    switch (u1) { case unit: }
    switch (u2) { case unit: }
    switch (u3) { case unit: }
}

@*/

struct lock *create_lock()
    //@ requires exists<predicate()>(?inv) &*& inv();
    //@ ensures lock(result, inv);
{
    //@ open exists(_);
    struct lock *lock = malloc(sizeof(struct lock));
    if (lock == 0) abort();
    lock->locked = 0;
    return lock;
    //@ close lock_inv(lock, inv)(unit);
    //@ produce_lemma_function_pointer_chunk(unit_le_refl) : le_refl<unit>(unit_le)(u) { call(); };
    //@ produce_lemma_function_pointer_chunk(unit_le_trans) : le_trans<unit>(unit_le)(u1, u2, u3) { call(); };
    //@ int id = create_tso(lock_inv(lock, inv), unit_le, cons(idf, nil), unit);
    //@ lock->tso_id = id;
    //@ close lock(lock, inv);
}

void lock_acquire(struct lock *lock)
    //@ requires [?f]lock(lock, ?inv);
    //@ ensures locked(lock, inv, f) &*& inv();
{
    for (;;)
        //@ invariant [f]lock(lock, inv);
    {
        //@ open lock(_, _);
        prophecy_id v0Id = create_tso_prophecy();
        //@ assert tso_prophecy(v0Id, ?v0);
        void *v;
        {
            /*@
            predicate P() = [f/2]lock->tso_id |-> _;
            predicate Q(unit u) = v0 == 0 ? [1/2]lock->frac |-> f &*& inv() : [f/2]lock->tso_id |-> _;
            lemma void ctxt(unit u)
                requires P() &*& unit_le(unit, u) == true &*& lock_inv(lock, inv)(u) &*& is_tso_cas_op(?op, &lock->locked, 0, (void *)1, v0, ?pre, ?post) &*& pre();
                ensures lock_inv(lock, inv)(unit) &*& unit_le(u, unit) == true &*& Q(unit) &*& is_tso_cas_op(op, &lock->locked, 0, (void *)1, v0, pre, post) &*& post();
            {
                open P();
                switch (u) { case unit: }
                open lock_inv(lock, inv)(u);
                op();
                if (v0 == 0) {
                    lock->frac = f;
                }
                close lock_inv(lock, inv)(u);
                close Q(unit);
            }
            @*/
            //@ produce_lemma_function_pointer_chunk(ctxt) : tso_cas_ctxt<unit>(&lock->locked, 0, (void *)1, v0, lock_inv(lock, inv), unit_le, unit, P, Q)(u) { call(); };
            //@ close P();
            v = tso_compare_and_swap(v0Id, &lock->locked, 0, (void *)1);
            //@ open Q(?u1);
            //@ switch (u1) { case unit: }
        }
        if (v == 0) {
            //@ close locked(lock, inv, f);
            break;
        }
    }
}

void lock_release(struct lock *lock)
    //@ requires locked(lock, ?inv, ?f) &*& inv();
    //@ ensures [f]lock(lock, inv);
{
    //@ open locked(lock, inv, f);
    {
        /*@
        predicate P() = [1/2]lock->frac |-> f &*& inv();
        predicate Q() = [f/2]lock->tso_id |-> _;
        lemma void ctxt(unit u1, unit u2)
            requires P() &*& unit_le(unit, u1) == true &*& unit_le(u1, u2) == true &*& lock_inv(lock, inv)(u2) &*& is_tso_write_op(?op, &lock->locked, 0, ?pre, ?post) &*& pre();
            ensures Q() &*& lock_inv(lock, inv)(unit) &*& unit_le(u2, unit) == true &*& unit_le(unit, unit) == true &*& is_tso_write_op(op, &lock->locked, 0, pre, post) &*& post();
        {
            open P();
            switch (u1) { case unit: }
            switch (u2) { case unit: }
            open lock_inv(lock, inv)(u2);
            assert lock_locked(lock, ?v0) &*& v0 != 0;
            op();
            close lock_inv(lock, inv)(unit);
            close Q();
        }
        @*/
        //@ produce_lemma_function_pointer_chunk(ctxt) : tso_write_ctxt<unit>(&lock->locked, 0, lock_inv(lock, inv), unit_le, unit, (idf)(nil), P, Q)(u1, u2) { call(); };
        //@ close P();
        tso_write(&lock->locked, 0, 0);
        //@ open Q();
    }
}

void lock_dispose(struct lock *lock)
    //@ requires lock(lock, ?inv);
    //@ ensures inv();
{
    //@ open lock(lock, inv);
    //@ tso_destroy();
    //@ open lock_inv(lock, inv)(_);
    free(lock);
}
