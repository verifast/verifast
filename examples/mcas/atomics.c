//@ #include <listex.gh>
#include <stdlib.h>
#include "popl20_prophecies.h"
#include "atomics.h"

/*@

predicate atomic_space(predicate() inv) = popl20_atomic_space(atomic_load_pointer, inv);

lemma void create_atomic_space(predicate() inv)
    requires inv();
    ensures atomic_space(inv);
{
    create_popl20_atomic_space(atomic_load_pointer, inv);
    close atomic_space(inv);
}

lemma void dispose_atomic_space(predicate() inv)
    nonghost_callers_only
    requires atomic_space(inv);
    ensures inv();
{
    open atomic_space(inv);
    dispose_popl20_atomic_space();
}

@*/

/*@

predicate prophecy_pointer(prophecy_id id, void *prophecy) =
    popl20_prophecy(id, ?vs) &*& 
    switch (vs) { case nil: return true; case cons(v0, vs0): return prophecy == (void *)(uintptr_t)fst(v0); };
    
@*/

prophecy_id create_prophecy_pointer()
    //@ requires true;
    //@ ensures prophecy_pointer(result, _);
{
    popl20_prophecy_id id = create_popl20_prophecy();
    //@ assert popl20_prophecy(id, ?vs);
    /*@
    switch (vs) {
    case nil:
        close prophecy_pointer(id, 0);
    case cons(v0, vs0):
        close prophecy_pointer(id, (void *)(uintptr_t)fst(v0));
    }
    @*/
    return id;
}

void *atomic_load_pointer(prophecy_id prophecyId, void **pp)
    /*@
    requires
        [?f]atomic_space(?inv) &*& prophecy_pointer(prophecyId, ?prophecy) &*&
        is_atomic_load_pointer_context(?ctxt) &*&
        atomic_load_pointer_context_pre(ctxt)(inv, pp, prophecy);
    @*/
    /*@
    ensures
        [f]atomic_space(inv) &*&
        is_atomic_load_pointer_context(ctxt) &*&
        atomic_load_pointer_context_post(ctxt)() &*&
        result == prophecy;
    @*/
{
    void *result;
    {
        /*@
        predicate pre() =
            [f]atomic_space(inv) &*&
            prophecy_pointer(prophecyId, prophecy) &*&
            is_atomic_load_pointer_context(ctxt) &*& atomic_load_pointer_context_pre(ctxt)(inv, pp, prophecy);
        predicate post(void *result_) =
            [f]atomic_space(inv) &*&
            is_atomic_load_pointer_context(ctxt) &*& atomic_load_pointer_context_post(ctxt)() &*& result_ == prophecy;
        @*/
        /*@
	produce_lemma_function_pointer_chunk popl20_atomic_load_pointer_ctxt(pp, {resolve_cmd(prophecyId, {})}, pre, post)() {
	    open pre();
	    assert is_popl20_atomic_load_pointer_ghop(?ghop, pp, {resolve_cmd(prophecyId, {})}, ?P, ?Q);
	    {
		predicate_family_instance atomic_load_pointer_operation_pre(my_atomic_load_pointer_operation)(void *pp_, void *prophecy_) =
		    pp_ == pp &*& prophecy_ == prophecy &*&
		    is_popl20_atomic_load_pointer_ghop(ghop, pp, {resolve_cmd(prophecyId, {})}, P, Q) &*& P() &*& prophecy_pointer(prophecyId, prophecy);
		predicate_family_instance atomic_load_pointer_operation_post(my_atomic_load_pointer_operation)() =
		    is_popl20_atomic_load_pointer_ghop(ghop, pp, {resolve_cmd(prophecyId, {})}, P, Q) &*& Q(prophecy);
		lemma void my_atomic_load_pointer_operation() : atomic_load_pointer_operation
		    requires atomic_load_pointer_operation_pre(my_atomic_load_pointer_operation)(?pp_, ?prophecy_) &*& [?f_]pointer(pp_, ?p);
		    ensures atomic_load_pointer_operation_post(my_atomic_load_pointer_operation)() &*& [f_]pointer(pp_, p) &*& p == prophecy_;
		{
		    open atomic_load_pointer_operation_pre(my_atomic_load_pointer_operation)(pp_, prophecy_);
		    open prophecy_pointer(prophecyId, prophecy);
		    assert popl20_prophecy(prophecyId, ?vs);
		    close prophecies({}, {});
		    close prophecies({resolve_cmd(prophecyId, {})}, {vs});
		    ghop();
		    open prophecies_resolved(_, _, _);
		    open prophecies_resolved(_, _, _);
		    close atomic_load_pointer_operation_post(my_atomic_load_pointer_operation)();
		    leak popl20_prophecy(_, _);
		}
		
		produce_lemma_function_pointer_chunk(my_atomic_load_pointer_operation) : atomic_load_pointer_operation()() {
		   call();
		} {
		    close atomic_load_pointer_operation_pre(my_atomic_load_pointer_operation)(pp, prophecy);
		    open atomic_space(inv);
		    popl20_open_atomic_space();
		    ctxt(my_atomic_load_pointer_operation);
		    popl20_close_atomic_space();
		    close [f]atomic_space(inv);
		    open atomic_load_pointer_operation_post(my_atomic_load_pointer_operation)();
		    assert Q(?result_);
		    close post(result_);
		}
	    }
	};
	@*/
	//@ close pre();
	resolve_list_id rlid = create_resolve_list();
	resolve_list_push(rlid, prophecyId);
        result = popl20_atomic_load_pointer(pp, rlid);
        //@ leak resolve_list(_, _);
        //@ open post(result);
    }
    return result;
}

void *atomic_compare_and_store_pointer(prophecy_id prophecyId, void **pp, void *old, void *new)
    /*@
    requires
        [?f]atomic_space(?inv) &*& prophecy_pointer(prophecyId, ?prophecy) &*&
        is_atomic_compare_and_store_pointer_context(?ctxt) &*&
        atomic_compare_and_store_pointer_context_pre(ctxt)(inv, pp, old, new, prophecy);
    @*/
    /*@
    ensures
        [f]atomic_space(inv) &*&
        is_atomic_compare_and_store_pointer_context(ctxt) &*&
        atomic_compare_and_store_pointer_context_post(ctxt)() &*&
        result == prophecy;
    @*/
{
    {
        /*@
        predicate pre() =
            [f]atomic_space(inv) &*&
            prophecy_pointer(prophecyId, prophecy) &*&
            is_atomic_compare_and_store_pointer_context(ctxt) &*&
            atomic_compare_and_store_pointer_context_pre(ctxt)(inv, pp, old, new, prophecy);
        predicate post(void *result) =
            [f]atomic_space(inv) &*&
            is_atomic_compare_and_store_pointer_context(ctxt) &*&
            atomic_compare_and_store_pointer_context_post(ctxt)() &*&
            result == prophecy;
        @*/
        /*@
        produce_lemma_function_pointer_chunk popl20_atomic_compare_and_swap_pointer_ctxt(pp, old, new, {resolve_cmd(prophecyId, {})}, pre, post)() {
            assert is_popl20_atomic_compare_and_swap_pointer_ghop(?ghop, pp, old, new, {resolve_cmd(prophecyId, {})}, ?P, ?Q);
            open pre();
            {
		predicate_family_instance atomic_compare_and_store_pointer_operation_pre(myop)(void **pp_, void *old_, void *new_, void *prophecy_) =
		    pp_ == pp &*& old_ == old &*& new_ == new &*& prophecy_ == prophecy &*&
		    is_popl20_atomic_compare_and_swap_pointer_ghop(ghop, pp, old, new, {resolve_cmd(prophecyId, {})}, P, Q) &*&
		    prophecy_pointer(prophecyId, prophecy) &*&
		    P();
		predicate_family_instance atomic_compare_and_store_pointer_operation_post(myop)() =
		    is_popl20_atomic_compare_and_swap_pointer_ghop(ghop, pp, old, new, {resolve_cmd(prophecyId, {})}, P, Q) &*&
		    Q(prophecy);
		lemma void myop() : atomic_compare_and_store_pointer_operation
		    requires
			atomic_compare_and_store_pointer_operation_pre(myop)(?pp_, ?old_, ?new_, ?prophecy_) &*&
			[?f_]pointer(pp_, ?p0) &*& p0 == old_ ? f_ == 1 : true;
		    ensures
			atomic_compare_and_store_pointer_operation_post(myop)() &*&
			[f_]pointer(pp_, ?p1) &*& p0 == prophecy_ &*&
			p1 == (p0 == old_ ? new_ : p0);
                {
                    open atomic_compare_and_store_pointer_operation_pre(myop)(_, _, _, _);
                    open prophecy_pointer(prophecyId, _);
                    popl20_prophecy_inv(prophecyId);
                    assert popl20_prophecy(prophecyId, ?vs);
                    close prophecies({}, {});
                    close prophecies({resolve_cmd(prophecyId, {})}, {vs});
                    ghop();
                    open prophecies_resolved(_, _, _);
                    open prophecies_resolved(_, _, _);
                    leak popl20_prophecy(prophecyId, _);
                    close atomic_compare_and_store_pointer_operation_post(myop)();
                }
                
                produce_lemma_function_pointer_chunk(myop) : atomic_compare_and_store_pointer_operation()() { call(); } {
                    close atomic_compare_and_store_pointer_operation_pre(myop)(pp, old, new, prophecy);
  		    open [f]atomic_space(inv);
  		    popl20_open_atomic_space();
                    ctxt(myop);
                    popl20_close_atomic_space();
                    close [f]atomic_space(inv);
                    open atomic_compare_and_store_pointer_operation_post(myop)();
                    assert Q(?result);
                    close post(result);
                }
            }
            
        };
        @*/
        //@ close pre();
        resolve_list_id rlid = create_resolve_list();
        resolve_list_push(rlid, prophecyId);
        void *result = popl20_atomic_compare_and_swap_pointer(pp, old, new, rlid);
        //@ leak resolve_list(_, _);
        //@ open post(result);
        return result;
    }
}

/*@

lemma void atomic_noop()
    nonghost_callers_only
    requires
        [?f]atomic_space(?inv) &*&
        is_atomic_noop_context(?ctxt) &*&
        atomic_noop_context_pre(ctxt)(inv);
    ensures
        [f]atomic_space(inv) &*&
        is_atomic_noop_context(ctxt) &*&
        atomic_noop_context_post(ctxt)();
{
    {
        predicate pre() = [f]atomic_space(inv) &*& is_atomic_noop_context(ctxt) &*& atomic_noop_context_pre(ctxt)(inv);
        predicate post() = [f]atomic_space(inv) &*& is_atomic_noop_context(ctxt) &*& atomic_noop_context_post(ctxt)();
        produce_lemma_function_pointer_chunk popl20_atomic_noop_ctxt(pre, post)() {
            open pre();
            open [f]atomic_space(inv);
            popl20_open_atomic_space();
            ctxt();
            popl20_close_atomic_space();
            close [f]atomic_space(inv);
            close post();
        };
        close pre();
        popl20_atomic_noop();
        open post();
    }
}

@*/

/*@

fixpoint bool is_successful(pair<int, list<vararg> > v) {
    switch (v) {
    case pair(result, marker): return length(marker) == 2 && head(marker) == vararg_pointer((void *)(uintptr_t)result);
    }
}

predicate_ctor cas_tracker_inv(struct cas_tracker *tracker)() =
    [_]tracker->pid |-> ?pid &*&
    [_]tracker->vs |-> ?vs &*&
    [1/2]tracker->count |-> ?count &*& 0 <= count &*& count <= length(vs) &*&
    popl20_prophecy(pid, ?vs1) &*& filter(is_successful, vs1) == drop(count, vs);

predicate cas_tracker(struct cas_tracker *tracker, int count) =
    [_]tracker->pid |-> ?pid &*&
    [_]tracker->vs |-> ?vs &*&
    [1/2]tracker->count |-> count &*& 0 <= count &*& count <= length(vs) &*&
    [_]popl20_atomic_space(create_cas_tracker, cas_tracker_inv(tracker));

predicate is_cas_tracker(struct cas_tracker *tracker;) =
    [_]tracker->pid |-> _ &*&
    [_]tracker->vs |-> _ &*&
    [_]popl20_atomic_space(create_cas_tracker, cas_tracker_inv(tracker));

lemma void cas_tracker_is_cas_tracker(struct cas_tracker *tracker)
    requires cas_tracker(tracker, ?n);
    ensures cas_tracker(tracker, n) &*& [_]is_cas_tracker(tracker);
{
    open cas_tracker(tracker, n);
    close is_cas_tracker(tracker);
    leak is_cas_tracker(tracker);
    close cas_tracker(tracker, n);
}

@*/

struct cas_tracker {
    popl20_prophecy_id pid;
    //@ list<pair<int, list<vararg> > > vs;
    //@ int count;
};

struct cas_tracker *create_cas_tracker()
    //@ requires true;
    //@ ensures cas_tracker(result, 0) &*& [_]is_cas_tracker(result);
{
    popl20_prophecy_id pid = create_popl20_prophecy();
    //@ assert popl20_prophecy(pid, ?vs);
    struct cas_tracker *tracker = malloc(sizeof(struct cas_tracker));
    if (tracker == 0) abort();
    tracker->pid = pid;
    //@ tracker->vs = filter(is_successful, vs);
    //@ tracker->count = 0;
    //@ leak tracker->pid |-> pid &*& tracker->vs |-> _ &*& malloc_block_cas_tracker(tracker);
    //@ close cas_tracker_inv(tracker)();
    //@ create_popl20_atomic_space(create_cas_tracker, cas_tracker_inv(tracker));
    //@ leak popl20_atomic_space(create_cas_tracker, cas_tracker_inv(tracker));
    //@ close cas_tracker(tracker, 0);
    //@ close is_cas_tracker(tracker);
    //@ leak is_cas_tracker(tracker);
    return tracker;
}

/*@

predicate tracked_cas_prediction(struct cas_tracker *tracker, int count; void *value) =
    [_]tracker->vs |-> ?vs &*&
    length(vs) <= count ?
        value == 0
    :
        switch (nth(count, vs)) {
        case pair(result, marker): return
            length(marker) < 2 ?
                value == 0
            :
                switch (nth(2, marker)) {
                case vararg_int(i): return value == 0;
                case vararg_uint(i): return value == 0;
                case vararg_pointer(p): return value == p;
                };
        };

lemma void *create_tracked_cas_prediction(struct cas_tracker *tracker, int count)
    requires [_]is_cas_tracker(tracker);
    ensures [_]tracked_cas_prediction(tracker, count, result);
{
    open is_cas_tracker(tracker);
    close tracked_cas_prediction(tracker, count, ?result);
    leak tracked_cas_prediction(tracker, count, result);
    return result;
}

@*/

void *tracked_cas(prophecy_id prophecyId, struct cas_tracker *tracker, void **pp, void *old, void *new)
    /*@
    requires
        [_]is_cas_tracker(tracker) &*&
        [?f]atomic_space(?inv) &*& prophecy_pointer(prophecyId, ?prophecy) &*&
        is_tracked_cas_ctxt(?ctxt) &*&
        tracked_cas_ctxt_pre(ctxt)(tracker, inv, pp, old, new, prophecy);
    @*/
    /*@
    ensures
        [_]is_cas_tracker(tracker) &*&
        [f]atomic_space(inv) &*&
        is_tracked_cas_ctxt(ctxt) &*&
        tracked_cas_ctxt_post(ctxt)() &*&
        result == prophecy;
    @*/
{
    //@ open is_cas_tracker(tracker);
    //@ popl20_prophecy_id pid = tracker->pid;
    resolve_list_id rlid = create_resolve_list();
    resolve_list_push(rlid, prophecyId);
    resolve_list_push(rlid, tracker->pid, old, new);
    //@ assert resolve_list(rlid, ?resolveCmds);
    {
        /*@
        predicate pre() =
            [f]atomic_space(inv) &*&
            [_]tracker->pid |-> pid &*& [_]is_cas_tracker(tracker) &*&
            prophecy_pointer(prophecyId, prophecy) &*&
            is_tracked_cas_ctxt(ctxt) &*&
            tracked_cas_ctxt_pre(ctxt)(tracker, inv, pp, old, new, prophecy);
        predicate post(void *result) =
            [f]atomic_space(inv) &*&
            is_tracked_cas_ctxt(ctxt) &*&
            tracked_cas_ctxt_post(ctxt)() &*&
            result == prophecy;
        @*/
        /*@
        produce_lemma_function_pointer_chunk popl20_atomic_compare_and_swap_pointer_ctxt(pp, old, new, resolveCmds, pre, post)() {
            assert is_popl20_atomic_compare_and_swap_pointer_ghop(?ghop, pp, old, new, resolveCmds, ?P, ?Q);
            open pre();
            open [f]atomic_space(inv);
            popl20_open_atomic_space();
            {
		predicate_family_instance tracked_cas_pre(myop)(struct cas_tracker *tracker_, void **pp_, void *old_, void *new_, void *prophecy_) =
		    tracker_ == tracker &*& pp_ == pp &*& old_ == old &*& new_ == new &*& prophecy_ == prophecy &*&
		    prophecy_pointer(prophecyId, prophecy) &*&
		    [_]tracker->pid |-> pid &*& [_]is_cas_tracker(tracker) &*&
		    popl20_atomic_spaces({pair(atomic_load_pointer, inv)}) &*&
		    is_popl20_atomic_compare_and_swap_pointer_ghop(ghop, pp, old, new, resolveCmds, P, Q) &*& P();
		predicate_family_instance tracked_cas_post(myop)() =
		    popl20_atomic_spaces({pair(atomic_load_pointer, inv)}) &*&
		    is_popl20_atomic_compare_and_swap_pointer_ghop(ghop, pp, old, new, resolveCmds, P, Q) &*& Q(prophecy);
		lemma void myop(int n, void *new0) : tracked_cas_operation
		    requires
			tracked_cas_pre(myop)(?tracker_, ?pp_, ?old_, ?new_, ?prophecy_) &*&
			[?f_]pointer(pp_, ?p0) &*&
			p0 == prophecy_ ?
			    p0 == old_ ?
				f_ == 1 &*& cas_tracker(tracker_, n) &*& [_]tracked_cas_prediction(tracker_, n, new0)
			    :
				true
			:
			    true;
		    ensures
			tracked_cas_post(myop)() &*&
			[f_]pointer(pp_, ?p1) &*& p0 == prophecy_ &*&
			p0 == old_ ? p1 == new_ &*& cas_tracker(tracker_, n + 1) &*& new0 == new_ : p1 == p0;
                {
                    open tracked_cas_pre(myop)(_, _, _, _, _);
                    open prophecy_pointer(prophecyId, _);
                    assert popl20_prophecy(prophecyId, ?prophecy_vs);
                    open is_cas_tracker(tracker);
                    popl20_open_atomic_space();
                    open cas_tracker_inv(tracker)();
                    assert popl20_prophecy(pid, ?tracker_vs1);
                    close prophecies({}, {});
                    close prophecies(tail(resolveCmds), {prophecy_vs});
                    close prophecies(resolveCmds, {tracker_vs1, prophecy_vs});
                    ghop();
                    open prophecies_resolved(_, _, _);
                    open prophecies_resolved(_, _, _);
                    open prophecies_resolved(_, _, _);
                    if (prophecy == old) {
                        open cas_tracker(tracker, ?count);
                        open tracked_cas_prediction(tracker, count, new0);
                        tracker->count++;
                        close cas_tracker(tracker, count + 1);
                        list<pair<int, list<vararg> > > tracker_vs = tracker->vs;
                        assert filter(is_successful, tail(tracker_vs1)) == drop(1, drop(count, tracker_vs));
                        length_drop(count, tracker_vs);
                        drop_n_plus_one(count, tracker_vs);
                        assert drop(count + 1, tracker_vs) == drop(1, drop(count, tracker_vs));
                    } else {
                    }
                    close cas_tracker_inv(tracker)();
                    popl20_close_atomic_space();
                    close tracked_cas_post(myop)();
                    leak popl20_prophecy(prophecyId, _);
                }
                produce_lemma_function_pointer_chunk(myop) : tracked_cas_operation()(n, new0) { call(); } {
                    close tracked_cas_pre(myop)(tracker, pp, old, new, prophecy);
                    ctxt(myop);
                    open tracked_cas_post(myop)();
                }
            }
            popl20_close_atomic_space();
            close [f]atomic_space(inv);
            close post(prophecy);
        };
        @*/
        //@ close pre();
        void *result = popl20_atomic_compare_and_swap_pointer(pp, old, new, rlid);
        //@ leak resolve_list(rlid, _);
        //@ open post(result);
        return result;
    }
}
