//@ #include "levels.gh"
//@ #include "obligations.gh"

#include <stdlib.h>
#include "threading_terminates.h"
#include "mutexes.h"
//@ #include "ghost_lists.gh"

struct mutex {
    semaphore semaphore;
    //@ int space;
    //@ int termScope;
    //@ real spaceFrac;
    //@ level level;
    //@ predicate() inv_;
    //@ int blockeesId;
    //@ int ownerToken;
    //@ int freeToken;
    //@ real freeTokenFrac;
};
typedef struct mutex *mutex;

/*@

fixpoint real real_sum(list<real> xs) {
    switch (xs) {
        case nil: return 0;
        case cons(x, xs0): return x + real_sum(xs0);
    }
}

predicate_ctor mutex_inv(mutex mutex, int termScope, real spaceFrac, semaphore semaphore, int scope, level level, predicate() inv, int blockeesId)() =
    [spaceFrac]term_perm(termScope, false) &*&
    semaphore(semaphore, ?items, ?blockees) &*&
    ghost_list<real>(blockeesId, ?blockeeFracs) &*& length(blockeeFracs) == blockees &*&
    [1/2]mutex->freeTokenFrac |-> ?ftf &*&
    items == 0 ?
        [ftf]mutex->freeToken |-> _ &*&
        [1 - real_sum(blockeeFracs)]obligation(scope, level)
    :
        [1/2]mutex->freeTokenFrac |-> ftf &*&
        mutex->ownerToken |-> _ &*& items == 1 &*& inv();

predicate mutex(mutex mutex; int space, int termScope, real spaceFrac, level level, predicate() inv) =
    mutex->semaphore |-> ?semaphore &*&
    mutex->space |-> space &*&
    mutex->termScope |-> termScope &*&
    mutex->spaceFrac |-> spaceFrac &*& [spaceFrac]obligation_space0(space, termScope) &*&
    mutex->level |-> level &*&
    mutex->inv_ |-> inv &*&
    mutex->blockeesId |-> ?blockeesId &*&
    malloc_block_mutex(mutex) &*&
    [_]ghost_cell<pair<int, real> >(space, pair(?scopeId, ?olevel)) &*&
    atomic_space(olevel + 1, mutex_inv(mutex, termScope, spaceFrac, semaphore, scopeId, level, inv, blockeesId)) &*&
    mutex->freeToken |-> _;

predicate mutex_held(mutex mutex, int space, int termScope, real spaceFrac, level level, predicate() inv, real frac) =
    [frac]mutex->semaphore |-> ?semaphore &*&
    [frac]mutex->space |-> space &*&
    [frac]mutex->termScope |-> termScope &*&
    [frac]mutex->spaceFrac |-> spaceFrac &*& [frac*spaceFrac]obligation_space0(space, termScope) &*&
    [frac]mutex->level |-> level &*&
    [frac]mutex->inv_ |-> inv &*&
    [frac]mutex->blockeesId |-> ?blockeesId &*&
    [frac]malloc_block_mutex(mutex) &*&
    [_]ghost_cell<pair<int, real> >(space, pair(?scopeId, ?olevel)) &*&
    [frac]atomic_space(olevel + 1, mutex_inv(mutex, termScope, spaceFrac, semaphore, scopeId, level, inv, blockeesId)) &*&
    mutex->ownerToken |-> _ &*&
    [1/2]mutex->freeTokenFrac |-> frac;

@*/

mutex create_mutex()
    //@ requires exists<real>(?fs) &*& [fs]obligation_space(?space, ?termScope) &*& exists<level>(?level) &*& exists<predicate()>(?inv) &*& inv();
    //@ ensures mutex(result, space, termScope, fs, level, inv);
    //@ terminates;
{
    //@ open exists(level);
    //@ open exists(inv);
    semaphore s = create_semaphore(1);
    mutex m = malloc(sizeof(struct mutex));
    if (m == 0) abort();
    m->semaphore = s;
    //@ m->space = space;
    //@ m->termScope = termScope;
    //@ m->spaceFrac = fs;
    //@ m->level = level;
    //@ m->inv_ = inv;
    //@ int blockeesId = create_ghost_list<real>();
    //@ m->blockeesId = blockeesId;
    //@ open obligation_space(space, termScope);
    //@ assert [_]ghost_cell<pair<int, real> >(space, pair(?scopeId, ?olevel));
    //@ close [fs]obligation_space0(space, termScope);
    //@ close mutex_inv(m, termScope, fs, s, scopeId, level, inv, blockeesId)();
    //@ create_atomic_space(olevel + 1, mutex_inv(m, termScope, fs, s, scopeId, level, inv, blockeesId));
    return m;
}

/*@

lemma void call_obligation_helper(real f)
    requires obligation_scope(?scope, ?p) &*& obligation_set(scope, ?obligations) &*& [f]obligation(scope, ?level) &*& level_all_above(obligations, level) == true;
    ensures obligation_scope(scope, p) &*& obligation_set_calling(scope, obligations, f, level) &*& p();
{
    call_obligation();
}

lemma void real_sum_append(list<real> xs, list<real> ys)
    requires true;
    ensures real_sum(append(xs, ys)) == real_sum(xs) + real_sum(ys);
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            real_sum_append(xs0, ys);
    }
}

lemma void dummy_lemma()
    requires true;
    ensures true;
{}

@*/

void mutex_acquire(mutex mutex)
    //@ requires [?f]mutex(mutex, ?space, ?termScope, ?fs, ?level, ?inv) &*& obspace_obligation_set(space, ?obs) &*& level_all_above(obs, level) == true;
    //@ ensures mutex_held(mutex, space, termScope, fs, level, inv, f) &*& obspace_obligation_set(space, cons(level, obs)) &*& inv();
    //@ terminates;
{
    //@ open [f]mutex(mutex, space, termScope, fs, level, inv);
    //@ semaphore s = mutex->semaphore;
    //@ int blockeesId = mutex->blockeesId;
    //@ open [f*fs]obligation_space0(space, termScope);
    //@ assert [_]ghost_cell<pair<int, real> >(space, pair(?scope, ?olevel));
    //@ open obspace_obligation_set(space, obs);
    {
        /*@
        predicate sep() = [f*fs]atomic_space(olevel, obligation_space_inv(scope, termScope));
        predicate unsep(int items, int blockees) =
            [fs]term_perm(termScope, false) &*&
            [f*fs]atomic_space(olevel, obligation_space_inv(scope, termScope)) &*&
            ghost_list<real>(blockeesId, ?blockeeFracs) &*& length(blockeeFracs) == blockees &*&
            [1/2]mutex->freeTokenFrac |-> ?ftf &*&
            items == 0 ?
                [ftf]mutex->freeToken |-> _ &*&
                [1 - real_sum(blockeeFracs)]obligation(scope, level)
            :
                [1/2]mutex->freeTokenFrac |-> _ &*& mutex->ownerToken |-> _ &*& items == 1 &*& inv();
        predicate P() = obligation_set(scope, obs) &*& [f]mutex->freeToken |-> _;
        predicate blocked() = ghost_list_member_handle<real>(blockeesId, ?frac) &*& obligation_set_calling(scope, obs, frac, level) &*& [f]mutex->freeToken |-> _;
        predicate Q() = obligation_set(scope, cons(level, obs)) &*& mutex->ownerToken |-> _ &*& inv() &*& [1/2]mutex->freeTokenFrac |-> f;
        lemma void sep()
            requires mutex_inv(mutex, termScope, fs, s, scope, level, inv, blockeesId)() &*& sep();
            ensures semaphore(s, ?items, ?blockees) &*& unsep(items, blockees);
        {
            open mutex_inv(mutex, termScope, fs, s, scope, level, inv, blockeesId)();
            open sep();

            assert semaphore(s, ?items, ?blockees);
            close unsep(items, blockees);
        }
        lemma void unsep()
            requires semaphore(s, ?items, ?blockees) &*& unsep(items, blockees);
            ensures mutex_inv(mutex, termScope, fs, s, scope, level, inv, blockeesId)() &*& sep();
        {
            open unsep(items, blockees);

            close mutex_inv(mutex, termScope, fs, s, scope, level, inv, blockeesId)();
            close sep();
        }
        lemma void block()
            requires atomic_space_level(olevel + 1) &*& unsep(0, ?blockees) &*& P();
            ensures atomic_space_level(olevel + 1) &*& unsep(0, blockees + 1) &*& blocked() &*& stop_perm(termScope);
        {
            open unsep(_, _);
            open P();

            assert ghost_list<real>(blockeesId, ?blockeeFracs);
            real fo = (1 - real_sum(blockeeFracs)) / 2;
            {
                predicate P1() = obligation_set(scope, obs) &*& [fo]obligation(scope, level);
                predicate Q1() = obligation_set_calling(scope, obs, fo, level) &*& stop_perm(termScope);
                lemma void body()
                    requires obligation_space_inv(scope, termScope)() &*& P1();
                    ensures obligation_space_inv(scope, termScope)() &*& Q1();
                {
                    open obligation_space_inv(scope, termScope)();
                    open P1();

                    call_obligation();

                    close Q1();
                    close obligation_space_inv(scope, termScope)();
                }
                produce_lemma_function_pointer_chunk(body) : atomic_noop_body(olevel, obligation_space_inv(scope, termScope), P1, Q1)() { call(); } {
                    close P1();
                    atomic_noop_nested();
                    open Q1();
                }
            }
            ghost_list_insert<real>(blockeesId, nil, blockeeFracs, (1 - real_sum(blockeeFracs)) / 2);

            close unsep(0, blockees + 1);
            close blocked();
        }
        lemma void unblock()
            requires atomic_space_level(olevel + 1) &*& unsep(0, ?blockees) &*& 0 < blockees &*& blocked() &*& stop_perm(termScope);
            ensures atomic_space_level(olevel + 1) &*& unsep(0, blockees - 1) &*& P();
        {
            open unsep(_, _);
            open blocked();

            assert ghost_list_member_handle<real>(blockeesId, ?frac);
            assert ghost_list<real>(blockeesId, ?blockeeFracs);
            ghost_list_match<real>();
            mem_remove_eq_append(frac, blockeeFracs);
            open exists(pair(?fs1, ?fs2));
            ghost_list_remove(blockeesId, fs1, fs2, frac);
            real_sum_append(fs1, cons(frac, fs2));
            real_sum_append(fs1, fs2);
            {
                predicate P1() = obligation_set_calling(scope, obs, frac, level) &*& stop_perm(termScope);
                predicate Q1() = obligation_set(scope, obs) &*& [frac]obligation(scope, level);
                lemma void body()
                    requires obligation_space_inv(scope, termScope)() &*& P1();
                    ensures obligation_space_inv(scope, termScope)() &*& Q1();
                {
                    open obligation_space_inv(scope, termScope)();
                    open P1();

                    return_obligation();

                    close Q1();
                    close obligation_space_inv(scope, termScope)();
                }
                produce_lemma_function_pointer_chunk(body) : atomic_noop_body(olevel, obligation_space_inv(scope, termScope), P1, Q1)() { call(); } {
                    close P1();
                    atomic_noop_nested();
                    open Q1();
                }
            }

            close unsep(0, blockees - 1);
            close P();
        }
        lemma void success()
            requires atomic_space_level(olevel + 1) &*& unsep(?items, 0) &*& 0 < items &*& P();
            ensures atomic_space_level(olevel + 1) &*& unsep(items - 1, 0) &*& Q();
        {
            open unsep(_, _);
            open P();

            {
                predicate P1() = obligation_set(scope, obs);
                predicate Q1() = obligation_set(scope, cons(level, obs)) &*& obligation(scope, level);
                lemma void body()
                    requires obligation_space_inv(scope, termScope)() &*& P1();
                    ensures obligation_space_inv(scope, termScope)() &*& Q1();
                {
                    open obligation_space_inv(scope, termScope)();
                    open P1();

                    create_obligation(level);

                    close Q1();
                    close obligation_space_inv(scope, termScope)();
                }
                produce_lemma_function_pointer_chunk(body) : atomic_noop_body(olevel, obligation_space_inv(scope, termScope), P1, Q1)() { call(); } {
                    close P1();
                    atomic_noop_nested();
                    open Q1();
                }
            }

            assert ghost_list<real>(blockeesId, ?blockeeFracs);
            switch (blockeeFracs) { case nil: case cons(h, t): }
            mutex->freeTokenFrac = f;

            close unsep(items - 1, 0);
            close Q();
        }
        @*/
        /*@
        produce_lemma_function_pointer_chunk(dummy_lemma) : inv_has_term_perm(termScope, mutex_inv(mutex, termScope, fs, s, scope, level, inv, blockeesId))() {
            call();
            open mutex_inv(mutex, termScope, fs, s, scope, level, inv, blockeesId)();
        };
        @*/
        //@ leak is_inv_has_term_perm(_, _, _);
        //@ produce_lemma_function_pointer_chunk(sep) : semaphore_sep(olevel + 1, mutex_inv(mutex, termScope, fs, s, scope, level, inv, blockeesId), s, sep, unsep)() { call(); };
        //@ produce_lemma_function_pointer_chunk(unsep) : semaphore_unsep(olevel + 1, mutex_inv(mutex, termScope, fs, s, scope, level, inv, blockeesId), s, sep, unsep)() { call(); };
        //@ produce_lemma_function_pointer_chunk(block) : semaphore_acquire_block(termScope, olevel + 1, unsep, P, blocked)() { call(); };
        //@ produce_lemma_function_pointer_chunk(unblock) : semaphore_acquire_unblock(termScope, olevel + 1, unsep, blocked, P)() { call(); };
        //@ produce_lemma_function_pointer_chunk(success) : semaphore_acquire_success(olevel + 1, unsep, P, Q)() { call(); };
        //@ close sep();
        //@ close P();
        //@ close exists(olevel + 1);
        semaphore_acquire(mutex->semaphore);
        //@ open Q();
        //@ open sep();
    }
    //@ close [f*fs]obligation_space0(space, termScope);
    //@ close mutex_held(mutex, space, termScope, fs, level, inv, f);
    //@ close obspace_obligation_set(space, cons(level, obs));
}

void mutex_release(mutex mutex)
    //@ requires mutex_held(mutex, ?space, ?termScope, ?fs, ?level, ?inv, ?f) &*& obspace_obligation_set(space, ?obs) &*& mem(level, obs) == true &*& inv();
    //@ ensures [f]mutex(mutex, space, termScope, fs, level, inv) &*& obspace_obligation_set(space, remove(level, obs));
    //@ terminates;
{
    //@ open mutex_held(mutex, space, termScope, fs, level, inv, f);
    //@ open [f*fs]obligation_space0(space, termScope);
    //@ open obspace_obligation_set(space, obs);
    //@ semaphore s = mutex->semaphore;
    //@ int blockeesId = mutex->blockeesId;
    //@ assert [_]ghost_cell<pair<int, real> >(space, pair(?scope, ?olevel));
    {
        /*@
        predicate sep() = [f*fs]atomic_space(olevel, obligation_space_inv(scope, termScope));
        predicate unsep(int items, int blockees) =
            [fs]term_perm(termScope, false) &*&
            [f*fs]atomic_space(olevel, obligation_space_inv(scope, termScope)) &*&
            ghost_list<real>(blockeesId, ?blockeeFracs) &*& length(blockeeFracs) == blockees &*&
            [1/2]mutex->freeTokenFrac |-> ?ftf &*&
            items == 0 ?
                [ftf]mutex->freeToken |-> _ &*&
                [1 - real_sum(blockeeFracs)]obligation(scope, level)
            :
                [1/2]mutex->freeTokenFrac |-> _ &*& mutex->ownerToken |-> _ &*& items == 1 &*& inv();
        predicate P() = obligation_set(scope, obs) &*& mutex->ownerToken |-> _ &*& inv() &*& [1/2]mutex->freeTokenFrac |-> f;
        predicate Q() =
            [f]atomic_space(olevel + 1, mutex_inv(mutex, termScope, fs, s, scope, level, inv, blockeesId)) &*&
            sep() &*&
            obligation_set(scope, remove(level, obs)) &*& [f]mutex->freeToken |-> _;
        lemma void sep()
            requires mutex_inv(mutex, termScope, fs, s, scope, level, inv, blockeesId)() &*& sep();
            ensures semaphore(s, ?items, ?blockees) &*& unsep(items, blockees);
        {
            open mutex_inv(mutex, termScope, fs, s, scope, level, inv, blockeesId)();
            open sep();

            assert semaphore(s, ?items, ?blockees);
            close unsep(items, blockees);
        }
        lemma void unsep()
            requires semaphore(s, ?items, ?blockees) &*& unsep(items, blockees);
            ensures mutex_inv(mutex, termScope, fs, s, scope, level, inv, blockeesId)() &*& sep();
        {
            open unsep(items, blockees);

            close mutex_inv(mutex, termScope, fs, s, scope, level, inv, blockeesId)();
            close sep();
        }
        lemma void success()
            requires atomic_space_level(olevel + 1) &*& semaphore(s, ?items, 0) &*& unsep(items - 1, 0) &*& P() &*& [f]atomic_space(olevel + 1, mutex_inv(mutex, termScope, fs, s, scope, level, inv, blockeesId));
            ensures atomic_space_level(olevel + 1) &*& mutex_inv(mutex, termScope, fs, s, scope, level, inv, blockeesId)() &*& Q();
        {
            open unsep(_, _);
            open P();
            
            assert items == 1;
            assert ghost_list<real>(blockeesId, ?blockeeFracs);
            switch (blockeeFracs) { case nil: case cons(h, t): }
            {
                predicate P1() = obligation_set(scope, obs) &*& obligation(scope, level);
                predicate Q1() = obligation_set(scope, remove(level, obs));
                lemma void body()
                    requires obligation_space_inv(scope, termScope)() &*& P1();
                    ensures obligation_space_inv(scope, termScope)() &*& Q1();
                {
                    open obligation_space_inv(scope, termScope)();
                    open P1();

                    destroy_obligation();

                    close Q1();
                    close obligation_space_inv(scope, termScope)();
                }
                produce_lemma_function_pointer_chunk(body) : atomic_noop_body(olevel, obligation_space_inv(scope, termScope), P1, Q1)() { call(); } {
                    close P1();
                    atomic_noop_nested();
                    open Q1();
                }
            }
            
            close unsep(items, 0);
            unsep();
            close Q();
        }
        @*/
        /*@
        produce_lemma_function_pointer_chunk(dummy_lemma) : inv_has_term_perm(termScope, mutex_inv(mutex, termScope, fs, s, scope, level, inv, blockeesId))() {
            call();
            open mutex_inv(mutex, termScope, fs, s, scope, level, inv, blockeesId)();
        };
        @*/
        //@ leak is_inv_has_term_perm(_, _, _);
        //@ produce_lemma_function_pointer_chunk(sep) : semaphore_sep(olevel + 1, mutex_inv(mutex, termScope, fs, s, scope, level, inv, blockeesId), s, sep, unsep)() { call(); };
        //@ produce_lemma_function_pointer_chunk(unsep) : semaphore_unsep(olevel + 1, mutex_inv(mutex, termScope, fs, s, scope, level, inv, blockeesId), s, sep, unsep)() { call(); };
        //@ produce_lemma_function_pointer_chunk(success) : semaphore_release(olevel + 1, mutex_inv(mutex, termScope, fs, s, scope, level, inv, blockeesId), s, unsep, f, P, Q)() { call(); };
        //@ close sep();
        //@ close P();
        semaphore_release(mutex->semaphore);
        //@ open Q();
        //@ open sep();
    }
    //@ close [f*fs]obligation_space0(space, termScope);
    //@ close [f]mutex(mutex, space, termScope, fs, level, inv);
    //@ close obspace_obligation_set(space, remove(level, obs));
}

void mutex_dispose(mutex mutex)
    //@ requires mutex(mutex, ?space, ?termScope, ?fs, ?level, ?inv);
    //@ ensures [fs]obligation_space(space, termScope) &*& inv();
    //@ terminates;
{
    //@ open mutex(_, _, _, _, _, _);
    //@ open obligation_space0(_, _);
    //@ semaphore s = mutex->semaphore;
    //@ int blockeesId = mutex->blockeesId;
    //@ assert [_]ghost_cell<pair<int, real> >(space, pair(?scope, ?olevel));
    //@ atomic_space_destroy(olevel + 1, mutex_inv(mutex, termScope, fs, s, scope, level, inv, blockeesId));
    //@ open mutex_inv(mutex, termScope, fs, s, scope, level, inv, blockeesId)();
    semaphore_dispose(mutex->semaphore);
    free(mutex);
    //@ close [fs]obligation_space(space, termScope);
    //@ leak ghost_list<real>(blockeesId, _);    
}

#endif
