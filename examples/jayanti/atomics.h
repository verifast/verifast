#ifndef ATOMICS_H
#define ATOMICS_H

/*@

predicate tracked_int(int id; int *pv, int v, int nbWrites);
predicate tracked_int_reads_tracker(int id; int nbReads);

lemma int start_tracking_int(int *pv);
    requires *pv |-> ?v;
    ensures tracked_int(result, pv, v, 0) &*& tracked_int_reads_tracker(result, 0);

lemma void stop_tracking_int(int id);
    requires tracked_int(id, ?pv, ?v, _) &*& tracked_int_reads_tracker(id, _);
    ensures *pv |-> v;

@*/

typedef long long prophecy_id;

/*@

predicate prophecy(prophecy_id prophecyId; int trackedIntId, int value, int nbWrites, int nbReads);

lemma void tracked_int_match_prophecy(prophecy_id prophecyId);
    requires [?fp]prophecy(prophecyId, ?trackedIntId, ?value, ?prophecyNbWrites, ?prophecyNbReads) &*& [?ft]tracked_int(trackedIntId, ?pv, ?v, ?nbWrites);
    ensures [fp]prophecy(prophecyId, trackedIntId, value, prophecyNbWrites, prophecyNbReads) &*& [ft]tracked_int(trackedIntId, pv, v, nbWrites) &*& nbWrites <= prophecyNbWrites;

lemma void tracked_int_reads_tracker_match_prophecy(prophecy_id prophecyId);
    requires [?fp]prophecy(prophecyId, ?trackedIntId, ?value, ?prophecyNbWrites, ?prophecyNbReads) &*& [?ft]tracked_int_reads_tracker(trackedIntId, ?nbReads);
    ensures [fp]prophecy(prophecyId, trackedIntId, value, prophecyNbWrites, prophecyNbReads) &*& [ft]tracked_int_reads_tracker(trackedIntId, nbReads) &*& nbReads <= prophecyNbReads;

@*/

prophecy_id create_prophecy();
    //@ requires exists<int>(?trackedIntId);
    //@ ensures prophecy(result, trackedIntId, ?value, ?nbWrites, ?nbReads);

/*@

predicate atomic_space(predicate() inv;);

lemma void create_atomic_space(predicate() inv);
    requires inv();
    ensures atomic_space(inv);

lemma void destroy_atomic_space();
    requires atomic_space(?inv);
    ensures inv();

@*/

/*@

typedef lemma void atomic_store_int_op(int prophecyId, int *pv, int value, predicate() P, predicate() Q)();
    requires
        prophecy(prophecyId, ?trackedIntId, ?prophecyValue, ?prophecyNbWrites, ?prophecyNbReads) &*&
        tracked_int(trackedIntId, pv, ?oldValue, ?nbWrites) &*& [?f]tracked_int_reads_tracker(trackedIntId, ?nbReads) &*& P();
    ensures tracked_int(trackedIntId, pv, value, nbWrites + 1) &*& [f]tracked_int_reads_tracker(trackedIntId, nbReads) &*& Q() &*&
        oldValue == prophecyValue &*& nbWrites == prophecyNbWrites &*& nbReads == prophecyNbReads;

typedef lemma void atomic_store_int_ghop(predicate() inv, int prophecyId, int *pv, int value, predicate() pre, predicate() post)();
    requires inv() &*& is_atomic_store_int_op(?op, prophecyId, pv, value, ?P, ?Q) &*& P() &*& pre();
    ensures inv() &*& is_atomic_store_int_op(op, prophecyId, pv, value, P, Q) &*& Q() &*& post();

@*/

void atomic_store_int(prophecy_id prophecyId, int *pv, int value);
    /*@
    requires
        [?f]atomic_space(?inv) &*&
        is_atomic_store_int_ghop(?ghop, inv, prophecyId, pv, value, ?pre, ?post) &*& pre();
    @*/
    /*@
    ensures
        [f]atomic_space(inv) &*&
        post();
    @*/

/*@

typedef lemma void atomic_load_int_op(int prophecyId, int *pv, predicate() P, predicate(int) Q)();
    requires
        prophecy(prophecyId, ?trackedIntId, ?prophecyValue, ?prophecyNbWrites, ?prophecyNbReads) &*&
        [?f]tracked_int(trackedIntId, pv, ?value, ?nbWrites) &*& tracked_int_reads_tracker(trackedIntId, ?nbReads) &*& P();
    ensures [f]tracked_int(trackedIntId, pv, value, nbWrites) &*& tracked_int_reads_tracker(trackedIntId, nbReads + 1) &*& Q(value) &*&
        value == prophecyValue &*& nbWrites == prophecyNbWrites &*& nbReads == prophecyNbReads;

typedef lemma void atomic_load_int_ghop(predicate() inv, int prophecyId, int *pv, predicate() pre, predicate(int) post)();
    requires inv() &*& is_atomic_load_int_op(?op, prophecyId, pv, ?P, ?Q) &*& P() &*& pre();
    ensures inv() &*& is_atomic_load_int_op(op, prophecyId, pv, P, Q) &*& Q(?result) &*& post(result);

@*/

int atomic_load_int(prophecy_id prophecyId, int *pv);
    /*@
    requires
        [?f]atomic_space(?inv) &*&
        is_atomic_load_int_ghop(?ghop, inv, prophecyId, pv, ?pre, ?post) &*& pre();
    @*/
    /*@
    ensures
        [f]atomic_space(inv) &*&
        post(result);
    @*/

#endif
