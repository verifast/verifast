#ifndef THREADING_WITH_OBSPACES_H
#define THREADING_WITH_OBSPACES_H

#include "threading_terminates.h"
//@ #include "obligation_spaces.gh"
//@ #include "listex.gh"

typedef void thread_run_with_obligations/*@(int termScope, int space, list<level> obs, predicate(void *) pre)@*/(void *data);
    //@ requires obspace_obligation_set(space, obs) &*& pre(data) &*& obspace_joinee(space);
    //@ ensures stop_perm(termScope);
    //@ terminates;

void thread_start_with_obligations(void *run, void *data);
    /*@
    requires
        [?fs]obligation_space(?space, ?termScope) &*&
        obspace_obligation_set(space, ?obs) &*&
        [_]is_thread_run_with_obligations(run, termScope, space, ?forkeeObs, ?pre) &*&
        call_perm_(currentThread, run) &*&
        length(remove_all(forkeeObs, obs)) + length(forkeeObs) == length(obs) &*&
        pre(data);
    @*/
    //@ ensures [fs]obligation_space(space, termScope) &*& obspace_obligation_set(space, remove_all(forkeeObs, obs));
    //@ terminates;

#endif
