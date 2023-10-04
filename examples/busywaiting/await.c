#include "await.h"

/*@

predicate_ctor wait_perm_(list<pathcomp> phase, void *f)(pair<void *, level> signal) =
    signal == pair(?s, ?level) &*&
    wait_perm(phase, s, level, f) &*& wait_perm(phase, s, level, await_core);

predicate wait_perm__(list<pathcomp> phase, void *signal, level level, void *f) = wait_perm(phase, signal, level, f);

@*/

void await_core(mutex mutex, condition *condition, void *data)
/*@
requires
    call_perm_(currentThread, condition) &*&
    obs(?phase0, ?obs) &*& [?f]mutex(mutex, ?level, ?inv) &*& [_]is_condition(condition, level, obs, inv, ?P, ?Q, ?R, ?signals) &*&
    foreach(signals, wait_perm_(phase0, condition)) &*&
    P(phase0, data) &*& is_await_viewshift(?awaitViewshift, R, inv, data, P) &*& forall(map(snd, obs), (all_sublevels_lt)(mutex_nb_level_dims, level)) == true;
@*/
//@ ensures obs(?phase1, obs) &*& [f]mutex(mutex, level, inv) &*& Q(phase1) &*& is_await_viewshift(awaitViewshift, R, inv, data, P);
//@ terminates;
{
    //@ is_ancestor_of_refl(phase0);
    for (;;)
    /*@
    invariant
        call_perm_(currentThread, condition) &*&
        obs(?phase1, obs) &*& [f]mutex(mutex, level, inv) &*& [_]is_condition(condition, level, obs, inv, P, Q, R, signals) &*& foreach(signals, wait_perm_(phase0, condition)) &*&
        is_ancestor_of(phase0, phase1) == true &*& P(phase1, data) &*& is_await_viewshift(awaitViewshift, R, inv, data, P);
    @*/
    {
        acquire(mutex);
        bool result;
        {
            result = condition(data);
        }
        //@ assert obs(?phase2, cons(?ob, obs));
        //@ is_ancestor_of_trans(phase0, phase1, phase2);
        if (result) {
            //@ assert signal(?s, ?sLevel, false);
            //@ foreach_remove(pair(s, sLevel), signals);
            //@ open wait_perm_(phase0, condition)(pair(s, sLevel));
            {
                /*@
                predicate pre() =
                    signal(s, sLevel, false) &*& R(phase2, data, s, sLevel) &*& is_await_viewshift(awaitViewshift, R, inv, data, P) &*&
                    wait_perm(phase0, s, sLevel, await_core) &*&
                    wait_perm(phase0, s, sLevel, condition);
                predicate post() = P(phase2, data) &*& call_perm_(currentThread, await_core) &*& call_perm_(currentThread, condition) &*&
                    is_await_viewshift(awaitViewshift, R, inv, data, P) &*&
                    wait_perm(phase0, s, sLevel, await_core) &*&
                    wait_perm(phase0, s, sLevel, condition);
                @*/
                /*@
                produce_lemma_function_pointer_chunk release_ghost_op(currentThread, phase2, obs, inv, pre, post)() {
                    open pre();
                    is_ancestor_of_refl(phase2);
                    close wait_perm__(phase0, s, sLevel, await_core);
                    wait(s);
                    open wait_perm__(phase0, s, sLevel, await_core);
                    close wait_perm__(phase0, s, sLevel, condition);
                    wait(s);
                    open wait_perm__(phase0, s, sLevel, condition);
                    awaitViewshift();
                    close post();
                };
                @*/
                //@ close pre();
                release_with_ghost_op(mutex);
                //@ open post();
            }
            //@ close wait_perm_(phase0, condition)(pair(s, sLevel));
            //@ foreach_unremove(pair(s, sLevel), signals);
        } else {
            release(mutex);
            break;
        }
    }
    //@ leak foreach(signals, wait_perm_(phase0, condition));
}

void await(mutex mutex, condition *condition, void *data)
/*@
requires
    call_perm_(currentThread, condition) &*&
    obs(?phase0, ?obs) &*& [?f]mutex(mutex, ?level, ?inv) &*& [_]is_condition(condition, level, obs, inv, ?P, ?Q, ?R, ?signals) &*&
    call_below_perms(length(signals), phase0, ?caller) &*& func_lt(condition, caller) == true &*&
    P(phase0, data) &*& is_await_viewshift(?awaitViewshift, R, inv, data, P) &*& forall(map(snd, obs), (all_sublevels_lt)(mutex_nb_level_dims, level)) == true;
@*/
//@ ensures obs(?phase1, obs) &*& [f]mutex(mutex, level, inv) &*& Q(phase1) &*& is_await_viewshift(awaitViewshift, R, inv, data, P);
{
    //@ close call_below_perms(0, phase0, await);
    /*@
    for (int i = 0; i < length(signals); i++)
        invariant obs(phase0, obs) &*& 0 <= i &*& i <= length(signals) &*& call_below_perms(i, phase0, await);
        decreases length(signals) - i;
    {
        produce_call_below_perm_();
        pathize_call_below_perm_();
        close call_below_perms(i + 1, phase0, await);
    }
    @*/
    {
        /*@
        lemma void iter(list<pair<void *, level> > signals1)
            requires call_below_perms(length(signals1), phase0, caller) &*& call_below_perms(length(signals1), phase0, await);
            ensures foreach(signals1, wait_perm_(phase0, condition));
        {
            switch (signals1) {
                case nil:
                    open call_below_perms(_, _, _);
                    open call_below_perms(_, _, _);
                    close foreach(nil, wait_perm_(phase0, condition));
                case cons(signals1head, signals1tail):
                    assert signals1head == pair(?s, ?sLevel);
                    open call_below_perms(length(signals1), phase0, caller);
                    create_wait_perm(s, sLevel, condition);
                    open call_below_perms(length(signals1), phase0, await);
                    create_wait_perm(s, sLevel, await_core);
                    iter(signals1tail);
                    close wait_perm_(phase0, condition)(pair(s, sLevel));
                    close foreach(signals1, wait_perm_(phase0, condition));
            }
        }
        @*/
        //@ iter(signals);
    }
    await_core(mutex, condition, data);
}

