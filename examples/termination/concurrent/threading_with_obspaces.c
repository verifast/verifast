#include <stdlib.h>
#include "threading_with_obspaces.h"
//@ #include "../call_perms.gh"

/*@

lemma void length_remove_all_ge<t>(list<t> xs, list<t> ys)
    requires true;
    ensures length(remove_all(xs, ys)) >= length(ys) - length(xs);
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            length_remove_all_ge(xs0, ys);
            length_remove(x0, remove_all(xs0, ys));
    }
}

lemma void create_obligation_(list<level> obligations, level level)
    requires obligation_scope(?scope, ?p) &*& obligation_set(scope, obligations);
    ensures obligation_scope(scope, p) &*& obligation_set(scope, cons(level, obligations)) &*& obligation(scope, level);
{
    create_obligation(level);
}

lemma void destroy_obligation_(list<level> obligations)
    requires obligation_scope(?scope, ?p) &*& obligation_set(scope, obligations) &*& obligation(scope, ?level) &*& mem(level, obligations) == true;
    ensures obligation_scope(scope, p) &*& obligation_set(scope, remove(level, obligations));
{
    destroy_obligation();
}

lemma void move_obligations(list<level> obs, list<level> forkeeObs)
    requires
        obligation_scope(?scope, ?termScope) &*&
        obligation_set(scope, obs) &*&
        obligation_set(scope, nil) &*&
        length(remove_all(forkeeObs, obs)) + length(forkeeObs) == length(obs);
    ensures
        obligation_scope(scope, termScope) &*&
        obligation_set(scope, remove_all(forkeeObs, obs)) &*&
        obligation_set(scope, forkeeObs);
{
    switch (forkeeObs) {
        case nil:
        case cons(fob, fobs):
            length_remove_all_ge(fobs, obs);
            length_remove(fob, remove_all(fobs, obs));
            move_obligations(obs, fobs);
            create_obligation_(fobs, fob);
            destroy_obligation_(remove_all(fobs, obs));
    }
}

@*/

struct closure {
    thread_run_with_obligations *run;
    void *data;
};

void run_closure(void *data)
    /*@
    requires
        closure_run(data, ?run_) &*&
        closure_data(data, ?runData_) &*&
        malloc_block_closure(data) &*&
        [_]is_thread_run_with_obligations(run_, ?termScope, ?space, ?forkeeObs, ?pre) &*&
        call_perm_(currentThread, run_) &*&
        [_]ghost_cell<pair<int, real> >(space, pair(?scope, ?olevel))
        &*& obspace_obligation_set(space, forkeeObs) &*&
        pre(runData_)
        &*& obligation_scope_joinee(scope);
    @*/
    //@ ensures stop_perm(termScope);
    //@ terminates;
{
    struct closure *closure = data;
    thread_run_with_obligations *run = closure->run;
    void *data_ = closure->data;
    free(closure);
    //@ close obspace_joinee(space);
    run(data_);
}

void thread_start_with_obligations(void *run, void *data)
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
{
    struct closure *closure = malloc(sizeof(struct closure)); // TODO: Eliminate closure by allowing function pointer in produce_function_pointer_chunk statement.
    if (closure == 0) abort();
    closure->run = run;
    closure->data = data;
    //@ open obligation_space(space, termScope);
    //@ assert [_]ghost_cell<pair<int, real> >(space, pair(?scope, ?olevel));
    {
        /*@
        predicate op_pre(int callPermScope, void *data_) =
            closure_run(data_, run) &*&
            closure_data(data_, data) &*&
            malloc_block_closure(data_) &*&
            [_]is_thread_run_with_obligations(run, termScope, space, forkeeObs, pre) &*&
            call_perm_(?thread, run) &*& call_perm_scope_of(thread) == callPermScope &*&
            [_]ghost_cell<pair<int, real> >(space, pair(scope, olevel))
            &*& obspace_obligation_set(space, obs) &*& pre(data);
        predicate forkerPost(void *data_) = obspace_obligation_set(space, remove_all(forkeeObs, obs));
        predicate forkeePost(int callPermScope, void *data_) =
            closure_run(data_, run) &*&
            closure_data(data_, data) &*&
            malloc_block_closure(data_) &*&
            [_]is_thread_run_with_obligations(run, termScope, space, forkeeObs, pre) &*&
            call_perm_(?thread, run) &*& call_perm_scope_of(thread) == callPermScope &*&
            [_]ghost_cell<pair<int, real> >(space, pair(scope, olevel))
            &*& obspace_obligation_set(space, forkeeObs) &*&
            pre(data)
            &*& obligation_scope_joinee(scope);
        lemma void op()
            requires obligation_space_inv(scope, termScope)() &*& op_pre(?callPermScope, closure) &*& stop_perm(termScope);
            ensures obligation_space_inv(scope, termScope)() &*& forkerPost(closure) &*& forkeePost(callPermScope, closure);
        {
            open obligation_space_inv(scope, termScope)();
            open op_pre(callPermScope, closure);
            open obspace_obligation_set(space, obs);
            
            join_obligation_scope(scope);
            move_obligations(obs, forkeeObs);
            
            close obspace_obligation_set(space, remove_all(forkeeObs, obs));
            close obspace_obligation_set(space, forkeeObs);
            close obligation_space_inv(scope, termScope)();
            close forkerPost(closure);
            close forkeePost(callPermScope, closure);
        }
        @*/
        //@ produce_lemma_function_pointer_chunk(op) : thread_start_ghost_op(termScope, obligation_space_inv(scope, termScope), closure, op_pre, forkerPost, forkeePost)() { call(); };
        //@ close op_pre(call_perm_scope_of(currentThread), closure);
        /*@
        produce_function_pointer_chunk thread_run(run_closure)(termScope, forkeePost)(data_) {
            open forkeePost(_, data_);
            call_perm__transfer(currentThread);
            call();
        }
        @*/
        //@ produce_call_below_perm_();
        //@ call_below_perm__elim(thread_start_with_obligations);
        //@ consume_call_perm_for(run_closure);
        thread_start(run_closure, closure);
        //@ open forkerPost(closure);
    }
    //@ close [fs]obligation_space(space, termScope);
}
