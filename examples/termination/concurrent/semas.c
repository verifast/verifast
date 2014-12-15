#include <stdlib.h>
#include "semas.h"

//@ #include "listex.gh"
//@ #include "splittable_counting.gh"

/*

Deadlock-preventing specification approach based on [K.R.M. Leino, P. Mueller, J. Smans. Deadlock-free channels and locks. ESOP 2010].

*/

struct sema {
    semaphore semaphore;
    //@ int space;
    //@ int termScope;
    //@ real spaceFrac;
    //@ level level;
    //@ int creditObject;
    //@ predicate() inv_;
    //@ int countingId;
};

/*@

lemma void mem_remove_eq_append<t>(t x, list<t> xs)
    requires mem(x, xs) == true;
    ensures exists(pair(?xs1, ?xs2)) &*& xs == append(xs1, cons(x, xs2)) &*& remove(x, xs) == append(xs1, xs2);
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            if (x0 == x) {
                close exists(pair(nil, xs0));
            } else {
                mem_remove_eq_append(x, xs0);
                open exists(pair(?xs1, ?xs2));
                close exists(pair(cons(x0, xs1), xs2));
            }
    }
}

lemma_auto void n_times_nonnegative()
    requires n_times(?n, ?p);
    ensures n_times(n, p) &*& 0 <= n;
{
    open n_times(_, _);
    if (n != 0)
        n_times_nonnegative();
    close n_times(n, p);
}

predicate_ctor sema_inv(sema sema, semaphore semaphore, int space, int termScope, real spaceFrac, level level, int creditObject, predicate() inv)() =
    [spaceFrac]term_perm(termScope, false) &*&
    semaphore(semaphore, ?items, ?blockees) &*&
    credit_object_handle(creditObject, items, blockees) &*&
    n_times(items, inv) &*&
    n_times(items, sema_release_token_(sema, space, termScope, level, creditObject, inv));

predicate sema(sema sema; int space, int termScope, real spaceFrac, level level, int creditObject, predicate() inv, int countingId) =
    sema->semaphore |-> ?semaphore &*&
    sema->space |-> space &*&
    sema->termScope |-> termScope &*&
    sema->spaceFrac |-> spaceFrac &*&
    sema->level |-> level &*&
    sema->creditObject |-> creditObject &*&
    sema->inv_ |-> inv &*&
    sema->countingId |-> countingId &*&
    obspace(spaceFrac, space, termScope) &*&
    malloc_block_sema(sema) &*&
    [_]ghost_cell<pair<int, real> >(space, pair(?scope, ?olevel)) &*&
    atomic_space(olevel + 2, sema_inv(sema, semaphore, space, termScope, spaceFrac, level, creditObject, inv));

predicate obspace(real f, int space, int termScope;) = [f]obligation_space0(space, termScope);

predicate_ctor sema_(sema sema)(;) = [1/2]sema(sema, _, _, _, _, _, _, _);

predicate sema_handle(sema sema, real frac, int space, int termScope, real spaceFrac, level level, int creditObject, predicate() inv, int releaseTokens) =
    [frac/2]sema(sema, space, termScope, spaceFrac, level, creditObject, inv, ?countingId) &*& 0 < frac &*&
    [_]obspace_credit_object_info(creditObject, space, level) &*&
    counting_handle(countingId, sema_(sema), frac, releaseTokens);

predicate_ctor sema_release_token_(sema sema, int space, int termScope, level level, int creditObject, predicate() inv)() =
    sema_release_token(sema, space, termScope, level, creditObject, inv);

predicate sema_release_token(sema sema, int space, int termScope, level level, int creditObject, predicate() inv) =
    [?f]sema(sema, space, termScope, ?fs, level, creditObject, inv, ?countingId) &*& 0 < f &*&
    [_]obspace_credit_object_info(creditObject, space, level) &*&
    counting_ticket(countingId, 2*f);

lemma void real_mul_pos(real x, real y);
    requires 0 < x &*& 0 < y;
    ensures 0 < x * y;

lemma void sema_create_release_token(sema sema)
    nonghost_callers_only
    requires sema_handle(sema, ?f, ?space, ?termScope, ?fs, ?level, ?creditObject, ?inv, ?releaseTokens);
    ensures sema_handle(sema, f, space, termScope, fs, level, creditObject, inv, releaseTokens + 1) &*& sema_release_token(sema, space, termScope, level, creditObject, inv);
{
    open sema_handle(sema, f, space, termScope, fs, level, creditObject, inv, releaseTokens);
    assert counting_handle(?countingId, _, _, _);
    create_counting_ticket(countingId);
    open [?frac]sema_(sema)();
    close sema_handle(sema, f, space, termScope, fs, level, creditObject, inv, releaseTokens + 1);
    close sema_release_token(sema, space, termScope, level, creditObject, inv);
}

lemma void sema_handle_split(sema sema, real f1, int releaseTokens1)
    nonghost_callers_only
    requires sema_handle(sema, ?f, ?space, ?termScope, ?fs, ?level, ?creditObject, ?inv, ?releaseTokens) &*& 0 < f1 &*& f1 < f;
    ensures sema_handle(sema, f1, space, termScope, fs, level, creditObject, inv, releaseTokens1) &*& sema_handle(sema, f - f1, space, termScope, fs, level, creditObject, inv, releaseTokens - releaseTokens1);
{
    open sema_handle(sema, f, space, termScope, fs, level, creditObject, inv, releaseTokens);
    assert counting_handle(?countingId, _, _, _);
    split_counting_handle(countingId, f1, releaseTokens1);
    close sema_handle(sema, f1, space, termScope, fs, level, creditObject, inv, releaseTokens1);
    close sema_handle(sema, f - f1, space, termScope, fs, level, creditObject, inv, releaseTokens - releaseTokens1);
}

lemma void sema_handle_merge(sema sema)
    nonghost_callers_only
    requires sema_handle(sema, ?f1, ?space1, ?termScope1, ?fs1, ?level1, ?creditObject1, ?inv1, ?releaseTokens1) &*& sema_handle(sema, ?f2, ?space2, ?termScope2, ?fs2, ?level2, ?creditObject2, ?inv2, ?releaseTokens2);
    ensures sema_handle(sema, f1 + f2, space1, termScope1, fs1, level1, creditObject1, inv1, releaseTokens1 + releaseTokens2) &*&
        space2 == space1 &*& termScope2 == termScope1 &*& fs2 == fs1 &*& level2 == level1 &*& creditObject2 == creditObject1 &*& inv2 == inv1;
{
    open sema_handle(sema, f1, space1, termScope1, fs1, level1, creditObject1, inv1, releaseTokens1);
    open sema_handle(sema, f2, space2, termScope2, fs2, level2, creditObject2, inv2, releaseTokens2);
    assert counting_handle(?countingId, _, _, _);
    merge_counting_handle(countingId);
    close sema_handle(sema, f1 + f2, space1, termScope1, fs1, level1, creditObject1, inv1, releaseTokens1 + releaseTokens2);
}

@*/

sema create_sema()
    //@ requires exists<real>(?fs) &*& [fs]obligation_space(?space, ?termScope) &*& obspace_credit_object(?creditObject, space, ?level, 0, 0) &*& exists<predicate()>(?inv);
    //@ ensures sema_handle(result, 1, space, termScope, fs, level, creditObject, inv, 0);
    //@ terminates;
{
    //@ obspace_credit_object_get_info();
    //@ open exists<predicate()>(inv);
    sema sema = malloc(sizeof(struct sema));
    if (sema == 0) abort();
    sema->semaphore = create_semaphore(0);
    //@ semaphore semaphore = sema->semaphore;
    //@ sema->space = space;
    //@ sema->termScope = termScope;
    //@ sema->spaceFrac = fs;
    //@ sema->level = level;
    //@ sema->creditObject = creditObject;
    //@ sema->inv_ = inv;
    //@ int countingId = create_counting_handle_id_reservation();
    //@ sema->countingId = countingId;
    //@ open [fs]obligation_space(space, termScope);
    //@ assert [_]ghost_cell<pair<int, real> >(space, pair(?scope, ?olevel));
    //@ close n_times(0, inv);
    //@ close n_times(0, sema_release_token_(sema, space, termScope, level, creditObject, inv));
    //@ open obspace_credit_object(creditObject, space, level, 0, 0);
    //@ close sema_inv(sema, sema->semaphore, space, termScope, fs, level, creditObject, inv)();
    //@ create_atomic_space(olevel + 2, sema_inv(sema, sema->semaphore, space, termScope, fs, level, creditObject, inv));
    return sema;
    //@ close [fs]obligation_space0(space, termScope);
    //@ close sema(sema, space, termScope, fs, level, creditObject, inv, countingId);
    //@ close sema_(sema)();
    //@ create_counting_handle(sema_(sema));
    //@ close sema_handle(sema, 1, space, termScope, fs, level, creditObject, inv, 0);
}

void sema_acquire(sema sema)
    /*@
    requires
        sema_handle(sema, ?f, ?space, ?termScope, ?fs, ?level, ?creditObject, ?inv, ?releaseTokens) &*&
        obspace_obligation_set(space, ?obs) &*& level_all_above(obs, level) == true &*&
        credit(creditObject);
    @*/
    /*@
    ensures
        sema_handle(sema, f, space, termScope, fs, level, creditObject, inv, releaseTokens - 1) &*&
        obspace_obligation_set(space, obs) &*&
        inv();
    @*/
    //@ terminates;
{
    //@ open sema_handle(sema, f, space, termScope, fs, level, creditObject, inv, releaseTokens);
    //@ open [f/2]sema(sema, space, termScope, fs, level, creditObject, inv, ?countingId);
    //@ open obspace(fs, space, termScope);
    //@ open [?fs_]obligation_space0(space, termScope);
    //@ open [_]obspace_credit_object_info(creditObject, space, level);
    //@ open obspace_obligation_set(space, obs);
    //@ semaphore s = sema->semaphore;
    //@ assert [_]ghost_cell<pair<int, real> >(space, pair(?scope, ?olevel));
    {
        /*@
        predicate sep() =
            [fs_]atomic_space(olevel, obligation_space_inv(scope, termScope)) &*&
            [_]atomic_space(olevel + 1, credit_object_(creditObject, scope, level)) &*&
            true;
        predicate unsep(int items, int blockees) =
            [fs_]atomic_space(olevel, obligation_space_inv(scope, termScope)) &*&
            [_]atomic_space(olevel + 1, credit_object_(creditObject, scope, level)) &*&
            [fs]term_perm(termScope, false) &*&
            credit_object_handle(creditObject, items, blockees) &*&
            n_times(items, inv) &*&
            n_times(items, sema_release_token_(sema, space, termScope, level, creditObject, inv));
        predicate P() = obligation_set(scope, obs) &*& credit(creditObject);
        predicate blocked() = obligation_set_calling(scope, obs, 1, level);
        predicate Q() = obligation_set(scope, obs) &*& inv() &*& sema_release_token(sema, space, termScope, level, creditObject, inv);
        lemma void sep()
            requires sema_inv(sema, s, space, termScope, fs, level, creditObject, inv)() &*& sep();
            ensures semaphore(s, ?items, ?blockees) &*& unsep(items, blockees);
        {
            open sema_inv(sema, s, space, termScope, fs, level, creditObject, inv)();
            open sep();

            assert semaphore(s, ?items, ?blockees);
            
            close unsep(items, blockees);
        }
        lemma void unsep()
            requires semaphore(s, ?items, ?blockees) &*& unsep(items, blockees);
            ensures sema_inv(sema, s, space, termScope, fs, level, creditObject, inv)() &*& sep();
        {
            open unsep(_, _);
            
            close sep();
            close sema_inv(sema, s, space, termScope, fs, level, creditObject, inv)();
        }
        lemma void block()
            requires atomic_space_level(olevel + 2) &*& unsep(0, ?blockees) &*& P();
            ensures atomic_space_level(olevel + 2) &*& unsep(0, blockees + 1) &*& blocked() &*& stop_perm(termScope);
        {
            open unsep(_, _);
            open P();

            {
                predicate P1() =
                    [fs_]atomic_space(olevel, obligation_space_inv(scope, termScope)) &*&
                    obligation_set(scope, obs) &*&
                    credit_object_handle(creditObject, 0, blockees) &*&
                    credit(creditObject);
                predicate Q1() =
                    [fs_]atomic_space(olevel, obligation_space_inv(scope, termScope)) &*&
                    credit_object_handle(creditObject, 0, blockees + 1) &*&
                    obligation_set_calling(scope, obs, 1, level) &*&
                    stop_perm(termScope);
                lemma void body()
                    requires atomic_space_level(olevel + 1) &*& credit_object_(creditObject, scope, level)() &*& P1();
                    ensures atomic_space_level(olevel + 1) &*& credit_object_(creditObject, scope, level)() &*& Q1();
                {
                    open credit_object_(creditObject, scope, level)();
                    open P1();

                    credit_object_block();
                    {
                        predicate P2() =
                            obligation_set(scope, obs) &*& obligation(scope, level);
                        predicate Q2() =
                            obligation_set_calling(scope, obs, 1, level) &*& stop_perm(termScope);
                        lemma void body2()
                            requires atomic_space_level(olevel) &*& obligation_space_inv(scope, termScope)() &*& P2();
                            ensures atomic_space_level(olevel) &*& obligation_space_inv(scope, termScope)() &*& Q2();
                        {
                            open obligation_space_inv(scope, termScope)();
                            open P2();

                            call_obligation();

                            close Q2();
                            close obligation_space_inv(scope, termScope)();
                        }
                        produce_lemma_function_pointer_chunk(body2) : atomic_noop_body(olevel, obligation_space_inv(scope, termScope), P2, Q2)() { call(); } {
                            close P2();
                            atomic_noop_nested();
                            open Q2();
                        }
                    }

                    close Q1();
                    close credit_object_(creditObject, scope, level)();
                }
                produce_lemma_function_pointer_chunk(body) : atomic_noop_body(olevel + 1, credit_object_(creditObject, scope, level), P1, Q1)() { call(); } {
                    close P1();
                    atomic_noop_nested();
                    open Q1();
                }
            }

            close unsep(0, blockees + 1);
            close blocked();
        }
        lemma void unblock()
            requires atomic_space_level(olevel + 2) &*& unsep(0, ?blockees) &*& 0 < blockees &*& blocked() &*& stop_perm(termScope);
            ensures atomic_space_level(olevel + 2) &*& unsep(0, blockees - 1) &*& P();
        {
            open unsep(_, _);
            open blocked();

            {
                predicate P1() =
                    [fs_]atomic_space(olevel, obligation_space_inv(scope, termScope)) &*&
                    obligation_set_calling(scope, obs, 1, level) &*&
                    credit_object_handle(creditObject, 0, blockees) &*&
                    stop_perm(termScope);
                predicate Q1() =
                    [fs_]atomic_space(olevel, obligation_space_inv(scope, termScope)) &*&
                    credit_object_handle(creditObject, 0, blockees - 1) &*&
                    obligation_set(scope, obs) &*&
                    credit(creditObject);
                lemma void body()
                    requires atomic_space_level(olevel + 1) &*& credit_object_(creditObject, scope, level)() &*& P1();
                    ensures atomic_space_level(olevel + 1) &*& credit_object_(creditObject, scope, level)() &*& Q1();
                {
                    open credit_object_(creditObject, scope, level)();
                    open P1();

                    {
                        predicate P2() =
                            obligation_set_calling(scope, obs, 1, level) &*& stop_perm(termScope);
                        predicate Q2() =
                            obligation_set(scope, obs) &*& obligation(scope, level);
                        lemma void body2()
                            requires atomic_space_level(olevel) &*& obligation_space_inv(scope, termScope)() &*& P2();
                            ensures atomic_space_level(olevel) &*& obligation_space_inv(scope, termScope)() &*& Q2();
                        {
                            open obligation_space_inv(scope, termScope)();
                            open P2();

                            return_obligation();

                            close Q2();
                            close obligation_space_inv(scope, termScope)();
                        }
                        produce_lemma_function_pointer_chunk(body2) : atomic_noop_body(olevel, obligation_space_inv(scope, termScope), P2, Q2)() { call(); } {
                            close P2();
                            atomic_noop_nested();
                            open Q2();
                        }
                    }
                    credit_object_unblock();

                    close Q1();
                    close credit_object_(creditObject, scope, level)();
                }
                produce_lemma_function_pointer_chunk(body) : atomic_noop_body(olevel + 1, credit_object_(creditObject, scope, level), P1, Q1)() { call(); } {
                    close P1();
                    atomic_noop_nested();
                    open Q1();
                }
            }

            close unsep(0, blockees - 1);
            close P();
        }
        lemma void acquire()
            requires atomic_space_level(olevel + 2) &*& unsep(?items, 0) &*& 0 < items &*& P();
            ensures atomic_space_level(olevel + 2) &*& unsep(items - 1, 0) &*& Q();
        {
            open unsep(_, _);
            open P();

            {
                predicate P1() =
                    credit_object_handle(creditObject, items, 0) &*&
                    credit(creditObject);
                predicate Q1() =
                    credit_object_handle(creditObject, items - 1, 0);
                lemma void body()
                    requires atomic_space_level(olevel + 1) &*& credit_object_(creditObject, scope, level)() &*& P1();
                    ensures atomic_space_level(olevel + 1) &*& credit_object_(creditObject, scope, level)() &*& Q1();
                {
                    open credit_object_(creditObject, scope, level)();
                    open P1();

                    credit_object_acquire();

                    close Q1();
                    close credit_object_(creditObject, scope, level)();
                }
                produce_lemma_function_pointer_chunk(body) : atomic_noop_body(olevel + 1, credit_object_(creditObject, scope, level), P1, Q1)() { call(); } {
                    close P1();
                    atomic_noop_nested();
                    open Q1();
                }
            }

            open n_times(items, inv);
            open n_times(items, sema_release_token_(sema, space, termScope, level, creditObject, inv));
            open sema_release_token_(sema, space, termScope, level, creditObject, inv)();
            close Q();
            close unsep(items - 1, 0);
        }
        lemma void dummy_lemma()
            requires true;
            ensures true;
        {}
        @*/
        /*@
        produce_lemma_function_pointer_chunk(dummy_lemma) : inv_has_term_perm(termScope, sema_inv(sema, s, space, termScope, fs, level, creditObject, inv))() {
            call();
            open sema_inv(sema, s, space, termScope, fs, level, creditObject, inv)();
        };
        @*/
        //@ leak is_inv_has_term_perm(_, _, _);
        //@ produce_lemma_function_pointer_chunk(sep) : semaphore_sep(olevel + 2, sema_inv(sema, s, space, termScope, fs, level, creditObject, inv), s, sep, unsep)() { call(); };
        //@ produce_lemma_function_pointer_chunk(unsep) : semaphore_unsep(olevel + 2, sema_inv(sema, s, space, termScope, fs, level, creditObject, inv), s, sep, unsep)() { call(); };
        //@ produce_lemma_function_pointer_chunk(block) : semaphore_acquire_block(termScope, olevel + 2, unsep, P, blocked)() { call(); };
        //@ produce_lemma_function_pointer_chunk(unblock) : semaphore_acquire_unblock(termScope, olevel + 2, unsep, blocked, P)() { call(); };
        //@ produce_lemma_function_pointer_chunk(acquire) : semaphore_acquire_success(olevel + 2, unsep, P, Q)() { call(); };
        //@ close sep();
        //@ close P();
        //@ close exists(olevel + 2);
        semaphore_acquire(sema->semaphore);
        //@ open sep();
        //@ open Q();
    }
    //@ close [fs_]obligation_space0(space, termScope);
    //@ close [f/2]obspace(fs, space, termScope);
    //@ close [f/2]sema(sema, space, termScope, fs, level, creditObject, inv, countingId);
    //@ open sema_release_token(sema, space, termScope, level, creditObject, inv);
    //@ assert counting_ticket(countingId, ?frac);
    //@ close [frac]sema_(sema)();
    //@ destroy_counting_ticket(countingId);
    //@ close sema_handle(sema, f, space, termScope, fs, level, creditObject, inv, releaseTokens - 1);
    //@ close obspace_obligation_set(space, obs);
}

void sema_release(sema sema)
    /*@
    requires
        sema_release_token(sema, ?space, ?termScope, ?level, ?creditObject, ?inv) &*& inv() &*&
        exists<bool>(?final) &*&
        final ?
            obspace_obligation_set(space, {level}) &*& debit(creditObject) &*& obspace_joinee(space) &*&
            ensures stop_perm(termScope)
        :
            ensures credit(creditObject);
    @*/
    //@ ensures true;
    //@ terminates;
{
    //@ open sema_release_token(sema, space, termScope, level, creditObject, inv);
    //@ assert counting_ticket(?countingId, ?f);
    //@ open [f/2]sema(sema, space, termScope, ?fs, level, creditObject, inv, countingId);
    //@ open [?fs_]obligation_space0(space, termScope);
    //@ open [_]obspace_credit_object_info(creditObject, space, _);
    semaphore s = sema->semaphore;
    //@ assert [_]ghost_cell<pair<int, real> >(space, pair(?scope, ?olevel));
    {
        /*@
        predicate sep() = true;
        predicate unsep(int items, int blockees) =
            [fs]term_perm(termScope, false) &*&
            credit_object_handle(creditObject, items, blockees) &*&
            n_times(items, inv) &*&
            n_times(items, sema_release_token_(sema, space, termScope, level, creditObject, inv));
        predicate P() =
            [fs_]atomic_space(olevel, obligation_space_inv(scope, termScope)) &*&
            [_]atomic_space(olevel + 1, credit_object_(creditObject, scope, level)) &*&
            [f/2]sema->semaphore |-> s &*&
            [f/2]sema->space |-> space &*&
            [f/2]sema->termScope |-> termScope &*&
            [f/2]sema->spaceFrac |-> fs &*&
            [f/2]sema->level |-> level &*&
            [f/2]sema->creditObject |-> creditObject &*&
            [f/2]sema->inv_ |-> inv &*&
            [f/2]sema->countingId |-> countingId &*&
            [f/2]malloc_block_sema(sema) &*&
            [_]ghost_cell<pair<int, real> >(space, pair(scope, olevel)) &*&
            [_]obspace_credit_object_info(creditObject, space, level) &*&
            counting_ticket(countingId, f) &*&
            inv() &*&
            final ?
                obspace_obligation_set(space, {level}) &*& debit(creditObject) &*& obspace_joinee(space)
            :
                true;
        predicate Q() =
            final ?
                stop_perm(termScope)
            :
                credit(creditObject);
        lemma void sep()
            requires sema_inv(sema, s, space, termScope, fs, level, creditObject, inv)() &*& sep();
            ensures semaphore(s, ?items, ?blockees) &*& unsep(items, blockees);
        {
            open sema_inv(sema, s, space, termScope, fs, level, creditObject, inv)();
            open sep();

            assert semaphore(s, ?items, ?blockees);
            
            close unsep(items, blockees);
        }
        lemma void unsep()
            requires semaphore(s, ?items, ?blockees) &*& unsep(items, blockees);
            ensures sema_inv(sema, s, space, termScope, fs, level, creditObject, inv)() &*& sep();
        {
            open unsep(_, _);
            
            close sep();
            close sema_inv(sema, s, space, termScope, fs, level, creditObject, inv)();
        }
        lemma void release()
            requires atomic_space_level(olevel + 2) &*& semaphore(s, ?items, 0) &*& unsep(items - 1, 0) &*& P() &*& [f/2]atomic_space(olevel + 2, sema_inv(sema, s, space, termScope, fs, level, creditObject, inv));
            ensures atomic_space_level(olevel + 2) &*& sema_inv(sema, s, space, termScope, fs, level, creditObject, inv)() &*& Q();
        {
            open unsep(_, _);
            open P();

            if (final) {
                open obspace_obligation_set(space, {level});
                open obspace_joinee(space);
            }

            {
                predicate P1() =
                    [fs_]atomic_space(olevel, obligation_space_inv(scope, termScope)) &*&
                    credit_object_handle(creditObject, items - 1, 0) &*&
                    final ?
                        obligation_set(scope, {level}) &*& debit(creditObject) &*& obligation_scope_joinee(scope)
                    :
                        true;
                predicate Q1() =
                    [fs_]atomic_space(olevel, obligation_space_inv(scope, termScope)) &*&
                    credit_object_handle(creditObject, items, 0) &*&
                    final ?
                        stop_perm(termScope)
                    :
                        credit(creditObject);
                lemma void body()
                    requires atomic_space_level(olevel + 1) &*& credit_object_(creditObject, scope, level)() &*& P1();
                    ensures atomic_space_level(olevel + 1) &*& credit_object_(creditObject, scope, level)() &*& Q1();
                {
                    open credit_object_(creditObject, scope, level)();
                    open P1();

                    credit_object_release();
                    if (final) {
                        debit_dispose();
                        {
                        predicate P2() =
                            obligation_set(scope, {level}) &*& obligation(scope, level) &*& obligation_scope_joinee(scope);
                        predicate Q2() =
                            stop_perm(termScope);
                        lemma void body2()
                            requires atomic_space_level(olevel) &*& obligation_space_inv(scope, termScope)() &*& P2();
                            ensures atomic_space_level(olevel) &*& obligation_space_inv(scope, termScope)() &*& Q2();
                        {
                            open obligation_space_inv(scope, termScope)();
                            open P2();

                            destroy_obligation();
                            leave_obligation_scope(scope);

                            close Q2();
                            close obligation_space_inv(scope, termScope)();
                        }
                        produce_lemma_function_pointer_chunk(body2) : atomic_noop_body(olevel, obligation_space_inv(scope, termScope), P2, Q2)() { call(); } {
                            close P2();
                            atomic_noop_nested();
                            open Q2();
                        }
                        }
                    }

                    close Q1();
                    close credit_object_(creditObject, scope, level)();
                }
                produce_lemma_function_pointer_chunk(body) : atomic_noop_body(olevel + 1, credit_object_(creditObject, scope, level), P1, Q1)() { call(); } {
                    close P1();
                    atomic_noop_nested();
                    open Q1();
                }
            }

            close n_times(items, inv);
            close [(f/2)*fs]obligation_space0(space, termScope);
            close [f/2]obspace(fs, space, termScope);
            close [f/2]sema(sema, space, termScope, fs, level, creditObject, inv, countingId);
            close sema_release_token(sema, space, termScope, level, creditObject, inv);
            close sema_release_token_(sema, space, termScope, level, creditObject, inv)();
            close n_times(items, sema_release_token_(sema, space, termScope, level, creditObject, inv));
            close Q();
            
            close sema_inv(sema, s, space, termScope, fs, level, creditObject, inv)();
        }
        lemma void dummy_lemma()
            requires true;
            ensures true;
        {}
        @*/
        /*@
        produce_lemma_function_pointer_chunk(dummy_lemma) : inv_has_term_perm(termScope, sema_inv(sema, s, space, termScope, fs, level, creditObject, inv))() {
            call();
            open sema_inv(sema, s, space, termScope, fs, level, creditObject, inv)();
        };
        @*/
        //@ leak is_inv_has_term_perm(_, _, _);
        //@ produce_lemma_function_pointer_chunk(sep) : semaphore_sep(olevel + 2, sema_inv(sema, s, space, termScope, fs, level, creditObject, inv), s, sep, unsep)() { call(); };
        //@ produce_lemma_function_pointer_chunk(unsep) : semaphore_unsep(olevel + 2, sema_inv(sema, s, space, termScope, fs, level, creditObject, inv), s, sep, unsep)() { call(); };
        //@ produce_lemma_function_pointer_chunk(release) : semaphore_release(olevel + 2, sema_inv(sema, s, space, termScope, fs, level, creditObject, inv), s, unsep, f/2, P, Q)() { call(); };
        //@ close sep();
        //@ close P();
        semaphore_release(s);
        //@ open Q();
    }
}

void sema_dispose(sema sema)
    //@ requires sema_handle(sema, 1, ?space, ?termScope, ?fs, ?level, ?creditObject, ?inv, 0);
    //@ ensures [fs]obligation_space(space, termScope) &*& obspace_credit_object(creditObject, space, level, 0, 0);
    //@ terminates;
{
    //@ open sema_handle(sema, 1, space, termScope, fs, level, creditObject, inv, 0);
    //@ open obspace_credit_object_info(creditObject, space, level);
    //@ assert counting_handle(?countingId, _, 1, 0);
    //@ destroy_counting_handle(countingId);
    //@ open sema_(sema)();
    //@ open sema(sema, space, termScope, fs, level, creditObject, inv, countingId);
    //@ semaphore semaphore = sema->semaphore;
    //@ open [fs]obligation_space0(space, termScope);
    //@ assert [_]ghost_cell<pair<int, real> >(space, pair(?scope, ?olevel));
    //@ atomic_space_destroy(olevel + 2, sema_inv(sema, sema->semaphore, space, termScope, fs, level, creditObject, inv));
    //@ open sema_inv(sema, sema->semaphore, space, termScope, fs, level, creditObject, inv)();
    //@ close [fs]obligation_space(space, termScope);
    //@ assert semaphore(semaphore, ?items, ?blockees);
    //@ close obspace_credit_object(creditObject, space, level, items, blockees);
    semaphore_dispose(sema->semaphore);
    //@ open n_times(items, sema_release_token_(sema, space, termScope, level, creditObject, inv));
    //@ open n_times(items, inv);
    /*@
    if (items != 0) {
        open sema_release_token_(sema, space, termScope, level, creditObject, inv)();
        open sema_release_token(sema, space, termScope, level, creditObject, inv);
        open sema(sema, space, termScope, _, level, creditObject, inv, _);
        
        assert false;
    }
    @*/
    free(sema);
}
