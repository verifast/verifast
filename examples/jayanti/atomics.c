//@ #include <listex.gh>
//@ #include <quantifiers.gh>
#include <stdlib.h>
#include "atomics.h"

struct int_tracker {
    popl20_prophecy_id pid;
    //@ list<pair<int, list<vararg> > > vs0;
    //@ int *pv;
    //@ int nbWrites;
    //@ int nbReads;
};

typedef struct int_tracker *int_tracker;

/*@

fixpoint bool is_write(pair<int, list<vararg> > v) {
    switch (v) {
    case pair(result, marker): return length(marker) == 2;
    }
}

predicate past_prophecy(pair<int, list<vararg> > v) =
    v == pair(?result, cons(vararg_pointer(?prophecyId), _)) &*&
    ((prophecy_id)prophecyId)->token |-> _;

predicate_ctor tracked_int_inv(int_tracker id)() =
    [_]id->pid |-> ?pid &*&
    [_]id->vs0 |-> ?vs0 &*&
    [_]id->pv |-> ?pv &*& [1/2]*pv |-> _ &*&
    [1/2]id->nbWrites |-> ?nbWrites &*& 0 <= nbWrites &*&
    [1/2]id->nbReads |-> ?nbReads &*& 0 <= nbReads &*&
    nbWrites + nbReads <= length(vs0) &*&
    nbWrites == length(filter(is_write, take(nbWrites + nbReads, vs0))) &*&
    foreach(take(nbWrites + nbReads, vs0), past_prophecy) &*&
    popl20_prophecy(pid, drop(nbWrites + nbReads, vs0));

predicate is_tracked_int(int_tracker id;) =
    [_]id->pid |-> ?pid &*&
    [_]id->vs0 |-> ?vs0 &*&
    [_]id->pv |-> ?pv &*&
    [_]popl20_atomic_space(start_tracking_int, tracked_int_inv(id));
predicate tracked_int(int_tracker id; int *pv, int v, int nbWrites) =
    [_]id->pid |-> ?pid &*&
    [_]id->vs0 |-> ?vs0 &*&
    [_]id->pv |-> pv &*& [1/2]*pv |-> v &*&
    [_]popl20_atomic_space(start_tracking_int, tracked_int_inv(id)) &*&
    [1/2]id->nbWrites |-> nbWrites;
predicate tracked_int_reads_tracker(struct int_tracker *id; int nbReads) =
    [_]id->pid |-> ?pid &*&
    [_]id->vs0 |-> ?vs0 &*&
    [_]id->pv |-> ?pv &*&
    [_]popl20_atomic_space(start_tracking_int, tracked_int_inv(id)) &*&
    [1/2]id->nbReads |-> nbReads;

@*/

int_tracker start_tracking_int(int *pv)
//@ requires *pv |-> ?v;
//@ ensures tracked_int(result, pv, v, 0) &*& tracked_int_reads_tracker(result, 0) &*& [_]is_tracked_int(result);
{
    popl20_prophecy_id pid = create_popl20_prophecy();
    //@ assert popl20_prophecy(pid, ?vs0);
    int_tracker tracker = malloc(sizeof(struct int_tracker));
    if (tracker == 0) abort();
    tracker->pid = pid;
    //@ tracker->vs0 = vs0;
    //@ tracker->pv = pv;
    //@ tracker->nbWrites = 0;
    //@ tracker->nbReads = 0;
    //@ leak tracker->pid |-> pid &*& tracker->vs0 |-> vs0 &*& tracker->pv |-> pv &*& malloc_block_int_tracker(tracker);
    //@ close foreach(nil, past_prophecy);
    //@ close tracked_int_inv(tracker)();
    //@ create_popl20_atomic_space(start_tracking_int, tracked_int_inv(tracker));
    //@ leak popl20_atomic_space(start_tracking_int, tracked_int_inv(tracker));
    //@ close tracked_int(tracker, pv, *pv, 0);
    //@ close tracked_int_reads_tracker(tracker, 0);
    //@ close is_tracked_int(tracker);
    //@ leak is_tracked_int(tracker);
    return tracker;
}

struct prophecy {
    int_tracker tracker;
    //@ unit token;
};

typedef struct prophecy *prophecy_id;

/*@

fixpoint int index_of_first<t>(fixpoint(t, bool) p, list<t> xs) {
    switch (xs) {
    case nil: return 0;
    case cons(x0, xs0): return p(x0) ? 0 : 1 + index_of_first(p, xs0);
    }
}

lemma void index_of_first_nonnegative<t>(fixpoint(t, bool) p, list<t> xs)
    requires true;
    ensures 0 <= index_of_first(p, xs) &*& index_of_first(p, xs) <= length(xs);
{
    switch (xs) {
    case nil:
    case cons(x0, xs0):
        index_of_first_nonnegative(p, xs0);
    }
}

lemma void nth_index_of_first_intro<t>(fixpoint(t, bool) p, list<t> xs)
    requires index_of_first(p, xs) < length(xs);
    ensures p(nth(index_of_first(p, xs), xs)) == true;
{
    switch (xs) {
    case nil:
    case cons(x0, xs0):
        if (!p(x0)) {
            index_of_first_nonnegative(p, xs0);
            nth_index_of_first_intro(p, xs0);
        }
    }
}

lemma void nth_index_of_first_elim<t>(int n, fixpoint(t, bool) p, list<t> xs)
    requires 0 <= n &*& n < length(xs) &*& p(nth(n, xs)) == true;
    ensures index_of_first(p, xs) <= n;
{
    switch (xs) {
    case nil:
    case cons(x0, xs0):
        if (n != 0)
            nth_index_of_first_elim(n - 1, p, xs0);
    }
}

fixpoint bool matches_prophecy_id(prophecy_id prophecyId, pair<int, list<vararg> > v) {
    switch (v) {
    case pair(result, marker): return marker != nil && head(marker) == vararg_pointer(prophecyId);
    }
}

inductive wrap<t> = wrap(t x);

predicate is_prophecy(prophecy_id prophecyId) =
    [_]prophecyId->tracker |-> ?trackedIntId &*& [_]is_tracked_int(trackedIntId);

predicate prophecy(prophecy_id prophecyId; int_tracker trackedIntId, int value, int nbWrites, int nbReads) =
    [_]prophecyId->tracker |-> trackedIntId &*&
    prophecyId->token |-> _ &*&
    [_]trackedIntId->vs0 |-> ?vs0 &*&
    wrap(index_of_first((matches_prophecy_id)(prophecyId), vs0)) == wrap(?index) &*&
    value == (index < length(vs0) ? fst(nth(index, vs0)) : 0) &*&
    nbWrites == length(filter(is_write, take(index, vs0))) &*&
    nbReads == index - nbWrites;

lemma void take_plus<t>(int m, int n, list<t> xs)
    requires 0 <= m &*& 0 <= n;
    ensures take(m + n, xs) == append(take(m, xs), take(n, drop(m, xs)));
{
    switch (xs) {
    case nil:
    case cons(x0, xs0):
        if (0 < m)
            take_plus(m - 1, n, xs0);
    }
}

lemma void filter_append<t>(fixpoint(t, bool) p, list<t> xs, list<t> ys)
    requires true;
    ensures filter(p, append(xs, ys)) == append(filter(p, xs), filter(p, ys));
{
    switch (xs) {
    case nil:
    case cons(x0, xs0):
        filter_append(p, xs0, ys);
    }
}

lemma void length_filter<t>(fixpoint(t, bool) p, list<t> xs)
    requires true;
    ensures length(filter(p, xs)) <= length(xs);
{
    switch (xs) {
    case nil:
    case cons(x0, xs0):
        length_filter(p, xs0);
    }
}

lemma void tracked_int_match_prophecy(prophecy_id prophecyId)
    requires
        popl20_atomic_spaces(?openSpaces) &*& forall(map(fst, openSpaces), (func_lt)(tracked_int_match_prophecy)) == true &*&
        [?fp]prophecy(prophecyId, ?trackedIntId, ?value, ?prophecyNbWrites, ?prophecyNbReads) &*& [?ft]tracked_int(trackedIntId, ?pv, ?v, ?nbWrites);
    ensures
        popl20_atomic_spaces(openSpaces) &*&
        [fp]prophecy(prophecyId, trackedIntId, value, prophecyNbWrites, prophecyNbReads) &*& [ft]tracked_int(trackedIntId, pv, v, nbWrites) &*& nbWrites <= prophecyNbWrites;
{
    open [fp]prophecy(prophecyId, trackedIntId, value, prophecyNbWrites, prophecyNbReads);
    open [ft]tracked_int(trackedIntId, pv, v, nbWrites);
    if (mem(pair(start_tracking_int, tracked_int_inv(trackedIntId)), openSpaces)) {
        mem_map(pair(start_tracking_int, tracked_int_inv(trackedIntId)), openSpaces, fst);
        forall_elim(map(fst, openSpaces), (func_lt)(tracked_int_match_prophecy), start_tracking_int);
        assert false;
    }
    popl20_open_atomic_space();
    open tracked_int_inv(trackedIntId)();
    assert [_]trackedIntId->vs0 |-> ?vs0;
    assert [_]trackedIntId->nbReads |-> ?nbReads;
    int index = index_of_first((matches_prophecy_id)(prophecyId), vs0);
    index_of_first_nonnegative((matches_prophecy_id)(prophecyId), vs0);
    if (index < nbWrites + nbReads) {
        nth_take(index, nbWrites + nbReads, vs0);
        mem_nth(index, take(nbWrites + nbReads, vs0));
        foreach_remove(nth(index, vs0), take(nbWrites + nbReads, vs0));
        open past_prophecy(nth(index, vs0));
        nth_index_of_first_intro((matches_prophecy_id)(prophecyId), vs0);
        assert false;
    }
    take_plus(nbWrites + nbReads, index - nbWrites - nbReads, vs0);
    filter_append(is_write, take(nbWrites + nbReads, vs0), take(index - nbWrites - nbReads, drop(nbWrites + nbReads, vs0)));
    assert length(filter(is_write, take(nbWrites + nbReads, vs0))) <= length(filter(is_write, take(index, vs0)));
    close tracked_int_inv(trackedIntId)();
    popl20_close_atomic_space();
}

lemma void tracked_int_reads_tracker_match_prophecy(prophecy_id prophecyId)
    requires
        popl20_atomic_spaces(?openSpaces) &*& forall(map(fst, openSpaces), (func_lt)(tracked_int_reads_tracker_match_prophecy)) == true &*&
        [?fp]prophecy(prophecyId, ?trackedIntId, ?value, ?prophecyNbWrites, ?prophecyNbReads) &*& [?ft]tracked_int_reads_tracker(trackedIntId, ?nbReads);
    ensures
        popl20_atomic_spaces(openSpaces) &*&
        [fp]prophecy(prophecyId, trackedIntId, value, prophecyNbWrites, prophecyNbReads) &*& [ft]tracked_int_reads_tracker(trackedIntId, nbReads) &*& nbReads <= prophecyNbReads;
{
    open [fp]prophecy(prophecyId, trackedIntId, value, prophecyNbWrites, prophecyNbReads);
    open [ft]tracked_int_reads_tracker(trackedIntId, nbReads);
    if (mem(pair(start_tracking_int, tracked_int_inv(trackedIntId)), openSpaces)) {
        mem_map(pair(start_tracking_int, tracked_int_inv(trackedIntId)), openSpaces, fst);
        forall_elim(map(fst, openSpaces), (func_lt)(tracked_int_reads_tracker_match_prophecy), start_tracking_int);
        assert false;
    }
    popl20_open_atomic_space();
    open tracked_int_inv(trackedIntId)();
    assert [_]trackedIntId->vs0 |-> ?vs0;
    assert [_]trackedIntId->nbWrites |-> ?nbWrites;
    int index = index_of_first((matches_prophecy_id)(prophecyId), vs0);
    index_of_first_nonnegative((matches_prophecy_id)(prophecyId), vs0);
    if (index < nbWrites + nbReads) {
        nth_take(index, nbWrites + nbReads, vs0);
        mem_nth(index, take(nbWrites + nbReads, vs0));
        foreach_remove(nth(index, vs0), take(nbWrites + nbReads, vs0));
        open past_prophecy(nth(index, vs0));
        nth_index_of_first_intro((matches_prophecy_id)(prophecyId), vs0);
        assert false;
    }
    take_plus(nbWrites + nbReads, index - nbWrites - nbReads, vs0);
    filter_append(is_write, take(nbWrites + nbReads, vs0), take(index - nbWrites - nbReads, drop(nbWrites + nbReads, vs0)));
    length_filter(is_write, take(nbWrites + nbReads, vs0));
    length_filter(is_write, take(index - nbWrites - nbReads, drop(nbWrites + nbReads, vs0)));
    length_take(index, vs0);
    close tracked_int_inv(trackedIntId)();
    popl20_close_atomic_space();
}

@*/

prophecy_id create_prophecy(int_tracker trackedIntId)
    //@ requires [_]is_tracked_int(trackedIntId);
    //@ ensures prophecy(result, trackedIntId, ?value, ?nbWrites, ?nbReads) &*& [_]is_prophecy(result);
{
    prophecy_id p = malloc(sizeof(struct prophecy));
    if (p == 0) abort();
    p->tracker = trackedIntId;
    //@ leak [_]p->tracker |-> trackedIntId &*& malloc_block_prophecy(p);
    //@ open is_tracked_int(trackedIntId);
    //@ close prophecy(p, trackedIntId, _, _, _);
    //@ close is_prophecy(p);
    //@ leak is_prophecy(p);
    return p;
}

/*

typedef lemma void atomic_store_int_op(prophecy_id prophecyId, int *pv, int value, predicate() P, predicate() Q)();
    requires
        popl20_atomic_spaces(?openSpaces) &*& forall(map(fst, openSpaces), (func_lt)(atomic_store_int_op)) == true &*&
        prophecy(prophecyId, ?trackedIntId, ?prophecyValue, ?prophecyNbWrites, ?prophecyNbReads) &*&
        tracked_int(trackedIntId, pv, ?oldValue, ?nbWrites) &*& [?f]tracked_int_reads_tracker(trackedIntId, ?nbReads) &*& P();
    ensures
        popl20_atomic_spaces(openSpaces) &*&
        tracked_int(trackedIntId, pv, value, nbWrites + 1) &*& [f]tracked_int_reads_tracker(trackedIntId, nbReads) &*& Q() &*&
        oldValue == prophecyValue &*& nbWrites == prophecyNbWrites &*& nbReads == prophecyNbReads;


typedef lemma void atomic_store_int_ghop(prophecy_id prophecyId, int *pv, int value, predicate() pre, predicate() post)();
    requires popl20_atomic_spaces(nil) &*& is_atomic_store_int_op(?op, prophecyId, pv, value, ?P, ?Q) &*& P() &*& pre();
    ensures popl20_atomic_spaces(nil) &*& is_atomic_store_int_op(op, prophecyId, pv, value, P, Q) &*& Q() &*& post();

*/

void atomic_store_int(prophecy_id prophecyId, int *pv, int value)
    /*@
    requires
        [_]is_prophecy(prophecyId) &*&
        is_atomic_store_int_ghop(?ghop, prophecyId, pv, value, ?pre, ?post) &*& pre();
    @*/
    /*@
    ensures
        post();
    @*/
{
    //@ open is_prophecy(prophecyId);
    resolve_list_id rlid = create_resolve_list();
    int_tracker trackedIntId = prophecyId->tracker;
    popl20_prophecy_id pid = trackedIntId->pid;
    resolve_list_push(rlid, pid, prophecyId, 0);
    //@ assert resolve_list(rlid, ?resolveCmds);
    {
        /*@
        predicate pre_() =
            is_atomic_store_int_ghop(ghop, prophecyId, pv, value, pre, post) &*& pre() &*& [_]prophecyId->tracker |-> trackedIntId &*& [_]trackedIntId->pid |-> pid;
        predicate post_() =
            post();
        @*/
        /*@
        produce_lemma_function_pointer_chunk popl20_atomic_store_int_ctxt(pv, value, resolveCmds, pre_, post_)() {
            assert is_popl20_atomic_store_int_ghop(?ghop_, pv, value, resolveCmds, ?P, ?Q);
            open pre_();
            {
                predicate P_() = is_popl20_atomic_store_int_ghop(ghop_, pv, value, resolveCmds, P, Q) &*& P() &*& [_]prophecyId->tracker |-> trackedIntId &*& [_]trackedIntId->pid |-> pid;
                predicate Q_() = is_popl20_atomic_store_int_ghop(ghop_, pv, value, resolveCmds, P, Q) &*& Q();
                produce_lemma_function_pointer_chunk atomic_store_int_op(prophecyId, pv, value, P_, Q_)() {
                    open P_();
                    open prophecy(prophecyId, _, ?prophecyValue, ?prophecyNbWrites, ?prophecyNbReads);
                    assert [_]trackedIntId->vs0 |-> ?vs0;
                    int index = index_of_first((matches_prophecy_id)(prophecyId), vs0);
                    open tracked_int(trackedIntId, pv, ?oldValue, ?nbWrites);
                    open [?f]tracked_int_reads_tracker(trackedIntId, ?nbReads);
                    assert popl20_atomic_spaces(?openSpaces);
                    if (mem(pair(start_tracking_int, tracked_int_inv(trackedIntId)), openSpaces)) {
                        mem_map(pair(start_tracking_int, tracked_int_inv(trackedIntId)), openSpaces, fst);
                        forall_mem(start_tracking_int, map(fst, openSpaces), (func_lt)(atomic_store_int));
                        assert false;
                    }
                    popl20_open_atomic_space();
                    open tracked_int_inv(trackedIntId)();
                    assert popl20_prophecy(pid, ?vs);
                    close prophecies({}, {});
                    close prophecies(resolveCmds, {vs});
                    ghop_();
                    open prophecies_resolved(_, _, _);
                    open prophecies_resolved(_, _, _);
                    trackedIntId->nbWrites++;
		    index_of_first_nonnegative((matches_prophecy_id)(prophecyId), vs0);
		    if (index < nbWrites + nbReads) {
			nth_take(index, nbWrites + nbReads, vs0);
			mem_nth(index, take(nbWrites + nbReads, vs0));
			foreach_remove(nth(index, vs0), take(nbWrites + nbReads, vs0));
			open past_prophecy(nth(index, vs0));
			nth_index_of_first_intro((matches_prophecy_id)(prophecyId), vs0);
			assert false;
		    }
                    drop_n_plus_one(nbWrites + nbReads, vs0);
		    assert matches_prophecy_id(prophecyId, nth(nbWrites + nbReads, vs0)) == true;
                    close tracked_int(trackedIntId, pv, value, nbWrites + 1);
                    close [f]tracked_int_reads_tracker(trackedIntId, nbReads);
                    take_plus(nbWrites + nbReads, 1, vs0);
                    filter_append(is_write, take(nbWrites + nbReads, vs0), take(1, drop(nbWrites + nbReads, vs0)));
                    close foreach(nil, past_prophecy);
                    close past_prophecy(pair(oldValue, {vararg_pointer(prophecyId), vararg_int(0)}));
                    close foreach({pair(oldValue, {vararg_pointer(prophecyId), vararg_int(0)})}, past_prophecy);
                    foreach_append(take(nbWrites + nbReads, vs0), {pair(oldValue, {vararg_pointer(prophecyId), vararg_int(0)})});
                    close tracked_int_inv(trackedIntId)();
                    popl20_close_atomic_space();
                    close Q_();
                    nth_index_of_first_elim(nbWrites + nbReads, (matches_prophecy_id)(prophecyId), vs0);
                    assert index < length(vs0);
                } {
                    close P_();
                    ghop();
                    open Q_();
                }
            }
            close post_();
            leak is_atomic_store_int_ghop(ghop, prophecyId, pv, value, pre, post);
        };
        @*/
        //@ close pre_();
        popl20_atomic_store_int(pv, value, rlid);
        //@ leak resolve_list(rlid, _);
        //@ open post_();
    }
}

/*

typedef lemma void atomic_load_int_op(prophecy_id prophecyId, int *pv, predicate() P, predicate(int) Q)();
    requires
        popl20_atomic_spaces(?openSpaces) &*& forall(map(fst, openSpaces), (func_lt)(atomic_store_int)) == true &*&
        prophecy(prophecyId, ?trackedIntId, ?prophecyValue, ?prophecyNbWrites, ?prophecyNbReads) &*&
        [?f]tracked_int(trackedIntId, pv, ?value, ?nbWrites) &*& tracked_int_reads_tracker(trackedIntId, ?nbReads) &*& P();
    ensures
        popl20_atomic_spaces(openSpaces) &*&
        [f]tracked_int(trackedIntId, pv, value, nbWrites) &*& tracked_int_reads_tracker(trackedIntId, nbReads + 1) &*& Q(value) &*&
        value == prophecyValue &*& nbWrites == prophecyNbWrites &*& nbReads == prophecyNbReads;

typedef lemma void atomic_load_int_ghop(prophecy_id prophecyId, int *pv, predicate() pre, predicate(int) post)();
    requires popl20_atomic_spaces(nil) &*& is_atomic_load_int_op(?op, prophecyId, pv, ?P, ?Q) &*& P() &*& pre();
    ensures popl20_atomic_spaces(nil) &*& is_atomic_load_int_op(op, prophecyId, pv, P, Q) &*& Q(?result) &*& post(result);

*/

int atomic_load_int(prophecy_id prophecyId, int *pv)
    /*@
    requires
        [_]is_prophecy(prophecyId) &*&
        is_atomic_load_int_ghop(?ghop, prophecyId, pv, ?pre, ?post) &*& pre();
    @*/
    /*@
    ensures
        post(result);
    @*/
{
    //@ open is_prophecy(prophecyId);
    resolve_list_id rlid = create_resolve_list();
    int_tracker trackedIntId = prophecyId->tracker;
    popl20_prophecy_id pid = trackedIntId->pid;
    resolve_list_push(rlid, pid, prophecyId);
    //@ assert resolve_list(rlid, ?resolveCmds);
    {
        /*@
        predicate pre_() =
            is_atomic_load_int_ghop(ghop, prophecyId, pv, pre, post) &*& pre() &*& [_]prophecyId->tracker |-> trackedIntId &*& [_]trackedIntId->pid |-> pid;
        predicate post_(int result) =
            post(result);
        @*/
        /*@
        produce_lemma_function_pointer_chunk popl20_atomic_load_int_ctxt(pv, resolveCmds, pre_, post_)() {
            assert is_popl20_atomic_load_int_ghop(?ghop_, pv, resolveCmds, ?P, ?Q);
            open pre_();
            {
                predicate P_() = is_popl20_atomic_load_int_ghop(ghop_, pv, resolveCmds, P, Q) &*& P() &*& [_]prophecyId->tracker |-> trackedIntId &*& [_]trackedIntId->pid |-> pid;
                predicate Q_(int result) = is_popl20_atomic_load_int_ghop(ghop_, pv, resolveCmds, P, Q) &*& Q(result);
                produce_lemma_function_pointer_chunk atomic_load_int_op(prophecyId, pv, P_, Q_)() {
                    open P_();
                    open prophecy(prophecyId, _, ?prophecyValue, ?prophecyNbWrites, ?prophecyNbReads);
                    assert [_]trackedIntId->vs0 |-> ?vs0;
                    int index = index_of_first((matches_prophecy_id)(prophecyId), vs0);
                    open [?f]tracked_int(trackedIntId, pv, ?oldValue, ?nbWrites);
                    open tracked_int_reads_tracker(trackedIntId, ?nbReads);
                    assert popl20_atomic_spaces(?openSpaces);
                    if (mem(pair(start_tracking_int, tracked_int_inv(trackedIntId)), openSpaces)) {
                        mem_map(pair(start_tracking_int, tracked_int_inv(trackedIntId)), openSpaces, fst);
                        forall_mem(start_tracking_int, map(fst, openSpaces), (func_lt)(atomic_store_int));
                        assert false;
                    }
                    popl20_open_atomic_space();
                    open tracked_int_inv(trackedIntId)();
                    assert [_]*pv |-> ?v;
                    assert popl20_prophecy(pid, ?vs);
                    close prophecies({}, {});
                    close prophecies(resolveCmds, {vs});
                    ghop_();
                    open prophecies_resolved(_, _, _);
                    open prophecies_resolved(_, _, _);
                    trackedIntId->nbReads++;
		    index_of_first_nonnegative((matches_prophecy_id)(prophecyId), vs0);
		    if (index < nbWrites + nbReads) {
			nth_take(index, nbWrites + nbReads, vs0);
			mem_nth(index, take(nbWrites + nbReads, vs0));
			foreach_remove(nth(index, vs0), take(nbWrites + nbReads, vs0));
			open past_prophecy(nth(index, vs0));
			nth_index_of_first_intro((matches_prophecy_id)(prophecyId), vs0);
			assert false;
		    }
                    drop_n_plus_one(nbWrites + nbReads, vs0);
		    assert matches_prophecy_id(prophecyId, nth(nbWrites + nbReads, vs0)) == true;
                    close [f]tracked_int(trackedIntId, pv, v, nbWrites);
                    close tracked_int_reads_tracker(trackedIntId, nbReads + 1);
                    take_plus(nbWrites + nbReads, 1, vs0);
                    filter_append(is_write, take(nbWrites + nbReads, vs0), take(1, drop(nbWrites + nbReads, vs0)));
                    close foreach(nil, past_prophecy);
                    close past_prophecy(pair(oldValue, {vararg_pointer(prophecyId)}));
                    close foreach({pair(oldValue, {vararg_pointer(prophecyId)})}, past_prophecy);
                    foreach_append(take(nbWrites + nbReads, vs0), {pair(oldValue, {vararg_pointer(prophecyId)})});
                    close tracked_int_inv(trackedIntId)();
                    popl20_close_atomic_space();
                    close Q_(v);
                    nth_index_of_first_elim(nbWrites + nbReads, (matches_prophecy_id)(prophecyId), vs0);
                    assert index < length(vs0);
                } {
                    close P_();
                    ghop();
                    open Q_(?result);
                    close post_(result);
                }
            }
            leak is_atomic_load_int_ghop(ghop, prophecyId, pv, pre, post);
        };
        @*/
        //@ close pre_();
        int result = popl20_atomic_load_int(pv, rlid);
        //@ leak resolve_list(rlid, _);
        //@ open post_(result);
        return result;
    }
}
