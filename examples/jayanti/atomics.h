#ifndef ATOMICS_H
#define ATOMICS_H

#include "popl20_prophecies.h"

struct int_tracker;
typedef struct int_tracker *int_tracker;

/*@

predicate is_tracked_int(int_tracker id;);
predicate tracked_int(int_tracker id; int *pv, int v, int nbWrites);
predicate tracked_int_reads_tracker(struct int_tracker *id; int nbReads);

@*/

int_tracker start_tracking_int(int *pv);
//@ requires *pv |-> ?v;
//@ ensures tracked_int(result, pv, v, 0) &*& tracked_int_reads_tracker(result, 0) &*& [_]is_tracked_int(result);

struct prophecy;
typedef struct prophecy *prophecy_id;

/*@

predicate is_prophecy(prophecy_id prophecyId);
predicate prophecy(prophecy_id prophecyId; int_tracker trackedIntId, int value, int nbWrites, int nbReads);

lemma void tracked_int_match_prophecy(prophecy_id prophecyId);
    requires
        popl20_atomic_spaces(?openSpaces) &*& forall(map(fst, openSpaces), (func_lt)(tracked_int_match_prophecy)) == true &*&
        [?fp]prophecy(prophecyId, ?trackedIntId, ?value, ?prophecyNbWrites, ?prophecyNbReads) &*& [?ft]tracked_int(trackedIntId, ?pv, ?v, ?nbWrites);
    ensures
        popl20_atomic_spaces(openSpaces) &*&
        [fp]prophecy(prophecyId, trackedIntId, value, prophecyNbWrites, prophecyNbReads) &*& [ft]tracked_int(trackedIntId, pv, v, nbWrites) &*& nbWrites <= prophecyNbWrites;

lemma void tracked_int_reads_tracker_match_prophecy(prophecy_id prophecyId);
    requires
        popl20_atomic_spaces(?openSpaces) &*& forall(map(fst, openSpaces), (func_lt)(tracked_int_reads_tracker_match_prophecy)) == true &*&
        [?fp]prophecy(prophecyId, ?trackedIntId, ?value, ?prophecyNbWrites, ?prophecyNbReads) &*& [?ft]tracked_int_reads_tracker(trackedIntId, ?nbReads);
    ensures
        popl20_atomic_spaces(openSpaces) &*&
        [fp]prophecy(prophecyId, trackedIntId, value, prophecyNbWrites, prophecyNbReads) &*& [ft]tracked_int_reads_tracker(trackedIntId, nbReads) &*& nbReads <= prophecyNbReads;

@*/

prophecy_id create_prophecy(int_tracker trackedIntId);
    //@ requires [_]is_tracked_int(trackedIntId);
    //@ ensures prophecy(result, trackedIntId, ?value, ?nbWrites, ?nbReads) &*& [_]is_prophecy(result);

/*@

typedef lemma void atomic_store_int_op(prophecy_id prophecyId, int *pv, int value, predicate() P, predicate() Q)();
    requires
        popl20_atomic_spaces(?openSpaces) &*& forall(map(fst, openSpaces), (func_lt)(atomic_store_int)) == true &*&
        prophecy(prophecyId, ?trackedIntId, ?prophecyValue, ?prophecyNbWrites, ?prophecyNbReads) &*&
        tracked_int(trackedIntId, pv, ?oldValue, ?nbWrites) &*& [?f]tracked_int_reads_tracker(trackedIntId, ?nbReads) &*& P();
    ensures
        popl20_atomic_spaces(openSpaces) &*&
        tracked_int(trackedIntId, pv, value, nbWrites + 1) &*& [f]tracked_int_reads_tracker(trackedIntId, nbReads) &*& Q() &*&
        oldValue == prophecyValue &*& nbWrites == prophecyNbWrites &*& nbReads == prophecyNbReads;

typedef lemma void atomic_store_int_ghop(prophecy_id prophecyId, int *pv, int value, predicate() pre, predicate() post)();
    requires popl20_atomic_spaces(nil) &*& is_atomic_store_int_op(?op, prophecyId, pv, value, ?P, ?Q) &*& P() &*& pre();
    ensures popl20_atomic_spaces(nil) &*& is_atomic_store_int_op(op, prophecyId, pv, value, P, Q) &*& Q() &*& post();

@*/

void atomic_store_int(prophecy_id prophecyId, int *pv, int value);
    /*@
    requires
        [_]is_prophecy(prophecyId) &*&
        is_atomic_store_int_ghop(?ghop, prophecyId, pv, value, ?pre, ?post) &*& pre();
    @*/
    /*@
    ensures
        post();
    @*/

/*@

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

@*/

int atomic_load_int(prophecy_id prophecyId, int *pv);
    /*@
    requires
        [_]is_prophecy(prophecyId) &*&
        is_atomic_load_int_ghop(?ghop, prophecyId, pv, ?pre, ?post) &*& pre();
    @*/
    /*@
    ensures
        post(result);
    @*/

#endif
