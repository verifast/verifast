// tab_size:2 verifast_options{I:../..}

// Justus Fasse and Bart Jacobs. Expressive modular verification of termination for busy-waiting programs. 2023.

#include <stdlib.h>
#include "cohortlock.h"
#include "ticketlock.h"
//@ #include <quantifiers.gh>
//@ #include "ghost_lists.gh"
//@ #include <ghost_cells.gh>

/*@

lemma a mem_map_mem<a, b>(b y, list<a> xs, fixpoint(a, b) f)
    requires mem(y, map(f, xs)) == true;
    ensures mem(result, xs) == true &*& f(result) == y;
{
    switch (xs) {
        case nil:
        case cons(x, xs0):
            if (f(x) == y)
                return x;
            else
                return mem_map_mem(y, xs0, f);
    }
}

lemma void note(bool b)
    requires b;
    ensures b;
{}

lemma void absurd(bool b)
    requires b &*& !b;
    ensures false;
{
}

fixpoint list<t> repeat<t>(nat n, t x) {
    switch (n) {
        case zero: return {};
        case succ(n0): return cons(x, repeat(n0, x));
    }
}

fixpoint list<int> zeros(int n) { return repeat(nat_of_int(n), 0); }

lemma void remove_eq_remove_nth_index_of<t>(t x, list<t> xs)
    requires mem(x, xs) == true;
    ensures remove(x, xs) == remove_nth(index_of(x, xs), xs);
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            if (x0 == x) {
            } else {
                remove_eq_remove_nth_index_of(x, xs0);
            }
    }
}

lemma void ghost_list_remove_remove<t>(int id, t x)
    requires ghost_list<t>(id, ?xs) &*& ghost_list_member_handle(id, x);
    ensures ghost_list<t>(id, remove(x, xs)) &*& mem(x, xs) == true;
{
    ghost_list_member_handle_lemma();
    mem_nth_index_of(x, xs);
    int n = index_of(x, xs);
    append_take_drop_n(xs, n);
    drop_n_plus_one(n, xs);
    nth_append_r(take(n, xs), drop(n, xs), 0);
    ghost_list_remove(id, take(n, xs), drop(n + 1, xs), x);
    drop_take_remove_nth(xs, n);
    remove_eq_remove_nth_index_of(x, xs);    
}

box_class incr_box(int i) {
  invariant true;
  action noop();
    requires true;
    ensures i == old_i;
  action incr();
    requires true;
    ensures i == old_i + 1;
  handle_predicate is_lower_bound(int j) {
    invariant j <= i;
    preserved_by noop() {}
    preserved_by incr() {}
  }
}

box_class growing_list0(list<int> xs) {
  invariant true;
  action noop();
    requires true;
    ensures xs == old_xs;
  action add(int elem);
    requires true;
    ensures xs == append(old_xs, {elem});
  handle_predicate has_at0(int k, int x) {
    invariant 0 <= k && k < length(xs) && nth(k, xs) == x;
    preserved_by noop() {}
    preserved_by add(elem) {
      nth_append(old_xs, {elem}, k);
    }
  }
}

predicate ghost_cells<t>(list<int> ids; list<t> values) =
    switch (ids) {
        case nil: return values == nil;
        case cons(id, ids0): return [_]ghost_cell<t>(id, ?value) &*& ghost_cells(ids0, ?values0) &*& values == cons(value, values0);
    };

lemma int ghost_cells_add<t>(t value)
    requires ghost_cells<t>(?ids, ?values);
    ensures ghost_cells<t>(append(ids, {result}), append(values, {value}));
{
    open ghost_cells(ids, values);
    int result;
    if (ids == nil) {
        result = create_ghost_cell(value);
        leak ghost_cell(result, value);
    } else {
        result = ghost_cells_add(value);
    }
    close ghost_cells(append(ids, {result}), append(values, {value}));
    return result;
}

lemma void ghost_cells_lookup<t>(int index)
    requires ghost_cells<t>(?ids, ?values) &*& 0 <= index &*& index < length(ids);
    ensures ghost_cells<t>(ids, values) &*& [_]ghost_cell<t>(nth(index, ids), nth(index, values));
{
    open ghost_cells(ids, values);
    if (index == 0) {
    } else {
        ghost_cells_lookup(index - 1);
    }
    close ghost_cells<t>(ids, values);
}

lemma void ghost_cells_match<t>(int index)
    requires ghost_cells<t>(?ids, ?values) &*& 0 <= index &*& index < length(ids) &*& [_]ghost_cell<t>(nth(index, ids), ?value);
    ensures ghost_cells<t>(ids, values) &*& nth(index, values) == value;
{
    open ghost_cells(ids, values);
    if (index == 0) {
        merge_fractions ghost_cell(nth(index, ids), _);
    } else {
        ghost_cells_match(index - 1);
    }
    close ghost_cells(ids, values);
}

predicate growing_list<t>(box id; list<t> elems) = growing_list0(id, ?ids) &*& ghost_cells(ids, elems) &*& length(ids) == length(elems);
predicate has_at<t>(handle h, box listId, int index, t elem) = has_at0(h, listId, index, ?id) &*& [_]ghost_cell(id, elem);

lemma box create_growing_list<t>()
    requires true;
    ensures growing_list<t>(result, {});
{
    create_box result = growing_list0({});
    close growing_list(result, {});
    return result;
}

lemma void growing_list_add<t>(box id, t value)
    requires growing_list<t>(id, ?elems);
    ensures growing_list<t>(id, append(elems, {value}));
{
    open growing_list(id, elems);
    int newId = ghost_cells_add(value);
    consuming_box_predicate growing_list0(id, ?ids)
    perform_action add(newId) {}
    producing_box_predicate growing_list0(append(ids, {newId}));
    close growing_list(id, append(elems, {value}));
}

lemma handle create_has_at<t>(box id, int index)
    requires growing_list<t>(id, ?elems) &*& 0 <= index &*& index < length(elems);
    ensures growing_list<t>(id, elems) &*& has_at<t>(result, id, index, nth(index, elems));
{
    open growing_list(id, elems);
    ghost_cells_lookup(index);
    consuming_box_predicate growing_list0(id, ?cellIds)
    perform_action noop() {}
    producing_fresh_handle_predicate has_at0(index, nth(index, cellIds));
    close growing_list<t>(id, elems);
    close has_at(?handleId, id, index, nth(index, elems));
    return handleId;
}

lemma void match_has_at_<t>(handle handleId)
    requires has_at<t>(handleId, ?id, ?index, ?elem) &*& growing_list<t>(id, ?elems);
    ensures growing_list<t>(id, elems) &*& has_at<t>(handleId, id, index, elem) &*& 0 <= index &*& index < length(elems) &*& nth(index, elems) == elem;
{
    open growing_list(id, elems);
    open has_at(handleId, id, index, elem);
    consuming_box_predicate growing_list0(id, ?elems0)
    consuming_handle_predicate has_at0(handleId, index, ?cellId)
    perform_action noop() {}
    producing_handle_predicate has_at0(handleId, index, cellId);
    ghost_cells_match(index);
    close growing_list(id, elems);
    close has_at(handleId, id, index, elem);
}

lemma void match_has_at<t>(box id)
    requires growing_list<t>(id, ?elems) &*& has_at<t>(?handleId, id, ?index, ?elem);
    ensures growing_list<t>(id, elems) &*& has_at<t>(handleId, id, index, elem) &*& 0 <= index &*& index < length(elems) &*& nth(index, elems) == elem;
{
    match_has_at_(handleId);
}

@*/

struct cohortlock {
  ticketlock lock;
  //@ predicate(int, bool) inv_;
  //@ int owner;
  //@ box ownerIncrBox;
  //@ bool held_;
  //@ box roundsInfoId; // A growing list that, at index I, has a tuple (C, CO0, LO0) where C is the owning cohort, GR0 is the initial client owner, LO0 is the initial local owner
};

struct cohort {
  cohortlock cohortlock;
  ticketlock lock;
  unsigned long long queueSize;
  //@ int queueSizeExcess; // The amount by which queueSize is greater than the actual size of the queue
  bool passing; // Passing ownership of the global lock to the next thread waiting for the cohort
  int passedCount; // Number of times ownershop of the global lock was passed within the cohort since the cohort most recently acquired the global lock
  //@ bool _passing;
  //@ int _passedCount;
  //@ bool releasing;
  //@ real lockFrac;
  //@ int owner;
  //@ bool held;
  //@ box enqueueIncrBoxId; // Counts the number of enqueue events
  //@ int queueListId; // Ghost list containing the signal identifiers of the threads waiting to acquire the local lock.
  //@ box waiteeListId; // Growing list. The signal at index I is the "designated waitee" between the I'th release and the I+1'th acquire.
  //@ box ownerSignalsId; // Growing list. The signal at index I is a pair (S, L). S is the signal held by the I'th owner before global beta is called the first time. L is a growing list containing one tuple (R, M, S) for each time global beta was called so far. R is the global round, M is the global M, and S is the signal held by the local owner after this call of global beta.
  //@ box globalOwnersId; // Growing list. For each local round I, the corresponding global round after the global lock is acquired.
  //@ box releaseSignalsId; // Growing list. For each local round I, the signal held between the release of the global lock and the release of the lock lock.
  //@ list<beta_call_info> betaCallsInfo;
};

#define MAX_PASS_COUNT 100

/*@

lemma void cohortlock_M_nb_dims_nonneg()
    requires true;
    ensures 0 <= cohortlock_M_nb_dims;
{
}

fixpoint level L() { return level(cohortlock_acquire, {}); }

inductive global_round_info = global_round_info(cohort ownerCohort, box enqueueIncrBoxId, int queueListId, box waiteeListId, box incrBoxId, box cohortHeldIncrBoxId, int initialClientOwner, int initialLocalOwner);

predicate_ctor cohortlock_inv(cohortlock lock, predicate(int, bool) inv, box ownerIncrBox, box roundsInfoId)() =
    [1/4]lock->owner |-> ?owner &*& 0 <= owner &*&
    incr_box(ownerIncrBox, owner) &*&
    [1/4]lock->held_ |-> ?held &*&
    growing_list<global_round_info>(roundsInfoId, ?roundsInfo) &*&
    length(roundsInfo) == owner + (held ? 1 : 0) &*&
    held ?
        nth(owner, roundsInfo) == global_round_info(?ownerCohort, ?enqueueIncrBoxId, ?queueListId, ?waiteeListId, ?incrBoxId, ?cohortHeldIncrBoxId, ?initialClientOwner, ?initialLocalOwner) &*&
        0 <= initialClientOwner &*& 0 <= initialLocalOwner &*&
        [1/2]ownerCohort->_passing |-> true &*&
        [1/2]ownerCohort->_passedCount |-> ?passedCount &*& 0 <= passedCount &*& passedCount <= MAX_PASS_COUNT &*&
        incr_box(incrBoxId, passedCount) &*&
        [1/4]ownerCohort->owner |-> ?cohortOwner &*& cohortOwner == initialLocalOwner + passedCount &*&
        [1/4]ownerCohort->held |-> ?cohortHeld &*&
        incr_box(cohortHeldIncrBoxId, passedCount + (cohortHeld ? 1 : 0)) &*&
        inv(initialClientOwner + passedCount, cohortHeld) &*&
        queue_info(ownerCohort, enqueueIncrBoxId, queueListId, waiteeListId, cohortOwner, cohortHeld, true)
    :
        [1/4]lock->owner |-> owner &*& [1/4]lock->held_ |-> held &*& inv(?clientOwner, false) &*& 0 <= clientOwner;

predicate_ctor cohortlock_ticketlock_inv(cohortlock lock)(int owner, bool held) =
    [1/2]lock->owner |-> owner &*&
    [1/2]lock->held_ |-> held;

predicate_ctor signal_pred(cohort cohort)(pair<void *, real> info) = info == pair(?s, ?f) &*& signal(s, L, false) &*& [f/2]cohort->queueListId |-> _;

inductive beta_call_info = beta_call_info(int globalOwner, list<int> M, void *signal, handle roundsInfoHandleId);

fixpoint bool beta_calls_info_decreases(list<beta_call_info> info, int i) {
    return
        i < 1 || length(info) <= i ||
        nth(i, info)->globalOwner == nth(i - 1, info)->globalOwner && nth(i, info)->M == nth(i - 1, info)->M ||
        lexprod_lt(nth(i, info)->M, nth(i - 1, info)->M);
}

lemma void beta_calls_info_mono(list<beta_call_info> info, int i, int j)
    requires forall_int((beta_calls_info_decreases)(info)) && 0 <= i &*& i < j &*& j < length(info);
    ensures
        nth(j, info)->globalOwner == nth(i, info)->globalOwner && nth(j, info)->M == nth(i, info)->M ||
        lexprod_lt(nth(j, info)->M, nth(i, info)->M);
{
    int k = i + 1;
    forall_int_elim((beta_calls_info_decreases)(info), i + 1);
    while (k < j)
        invariant i < k &*& k <= j &*&
            nth(k, info)->globalOwner == nth(i, info)->globalOwner && nth(k, info)->M == nth(i, info)->M ||
            lexprod_lt(nth(k, info)->M, nth(i, info)->M);
        decreases j - k;
    {
        forall_int_elim((beta_calls_info_decreases)(info), k + 1);
        if (lexprod_lt(nth(k + 1, info)->M, nth(k, info)->M) && lexprod_lt(nth(k, info)->M, nth(i, info)->M))
            lexprod_lt_trans(nth(k + 1, info)->M, nth(k, info)->M, nth(i, info)->M);
        k++;
    }
}

fixpoint bool global_owner_changed_ok(list<beta_call_info> info, list<bool> globalOwnerChangedList, int i) {
    return
        i < 1 || length(info) <= i || !nth(i - 1, globalOwnerChangedList) ||
        nth(i, info)->globalOwner > nth(i - 1, info)->globalOwner;
}

predicate queue_info(cohort cohort, box enqueueIncrBoxId, int queueListId, box waiteeListId, int owner, bool held, bool passing) =
    counter(&cohort->queueSize, ?queueSize) &*& 0 <= queueSize &*&
    [1/2]cohort->queueSizeExcess |-> ?queueSizeExcess &*& 0 <= queueSizeExcess &*& held || queueSizeExcess == 0 &*&
    ghost_list<pair<void *, real> >(queueListId, ?queue) &*& length(queue) + queueSizeExcess == queueSize &*& foreach(queue, signal_pred(cohort)) &*&
    incr_box(enqueueIncrBoxId, ?enqueueCount) &*& 0 <= enqueueCount &*& length(queue) == enqueueCount - owner - (held ? 1 : 0) &*&
    !passing || held || 0 < length(queue) &*&
    growing_list<void *>(waiteeListId, ?waitees) &*& length(waitees) == owner + (length(queue) == 0 && !held ? 0 : 1) &*&
    length(queue) == 0 && !passing || held || mem(nth(owner, waitees), map(fst, queue));

inductive owner_signal_info = owner_signal_info(void *ownerSignal, box betaCallsInfoId, box globalOwnerChangedListId);

predicate global_owner_changed_handle(handle globalOwnerChangedHandle) = true;

predicate passing_global_owner_handle(handle globalOwnerHandle) = true;

predicate_ctor cohort_inv(
        cohort cohort,
        cohortlock lock,
        predicate(int, bool) inv,
        ticketlock globalLock,
        real globalLockFrac,
        box ownerIncrBox,
        box roundsInfoId,
        box enqueueIncrBoxId,
        int queueListId,
        box waiteeListId,
        box ownerSignalsId,
        box globalOwnersId,
        box releaseSignalsId)() =
    [1/8]cohort->owner |-> ?owner &*& 0 <= owner &*&
    [1/8]cohort->held |-> ?held &*&
    [1/4]cohort->_passing |-> ?passing &*& (held ? true : cohort->passing |-> passing) &*&
    [1/4]cohort->_passedCount |-> ?passedCount &*& 0 <= passedCount &*& (held ? true : cohort->passedCount |-> passedCount) &*& passedCount <= MAX_PASS_COUNT &*&
    [1/2]cohort->releasing |-> ?releasing &*&
    growing_list<owner_signal_info>(ownerSignalsId, ?ownerSignals) &*& length(ownerSignals) == owner + (held ? 1 : 0) &*&
    growing_list<int>(globalOwnersId, ?globalOwners) &*& length(globalOwners) == owner + (passing || releasing ? 1 : 0) &*&
    growing_list<void *>(releaseSignalsId, ?releaseSignals) &*& length(releaseSignals) == owner + (releasing ? 1 : 0) &*&
    [globalLockFrac]atomic_space(create_cohortlock, cohortlock_inv(lock, inv, ownerIncrBox, roundsInfoId)) &*&
    (held ? true : [1/4]cohort->_passing |-> passing &*& [1/4]cohort->_passedCount |-> passedCount &*& [1/2]cohort->queueSizeExcess |-> 0 &*& [1/8]cohort->owner |-> owner &*& [1/8]cohort->held |-> held &*& [1/2]cohort->releasing |-> false) &*&
    (!passing && held && !releasing ? true : cohort->betaCallsInfo |-> _) &*&
    passing ?
        !releasing &*&
        [1/4]lock->owner |-> ?globalOwner &*& [1/4]lock->held_ |-> true &*&
        globalOwner == nth(owner, globalOwners) &*&
        (held ? true : ticketlock_held(globalLock, cohortlock_ticketlock_inv(lock), globalLockFrac, globalOwner)) &*&
        passing_global_owner_handle(?passingGlobalOwnerHandle) &*&
        has_at(passingGlobalOwnerHandle, roundsInfoId, globalOwner, global_round_info(cohort, enqueueIncrBoxId, queueListId, waiteeListId, ?incrBoxId, ?cohortHeldIncrBoxId, ?initialClientOwner, ?initialLocalOwner)) &*&
        owner == initialLocalOwner + passedCount
    :
        queue_info(cohort, enqueueIncrBoxId, queueListId, waiteeListId, owner, held, false) &*&
        [1/4]cohort->owner |-> owner &*&
        [1/4]cohort->held |-> held &*&
        [1/2]cohort->_passing |-> passing &*&
        [1/2]cohort->_passedCount |-> passedCount &*& passedCount == 0 &*&
        held ?
            !releasing ?
                nth(owner, ownerSignals) == owner_signal_info(?ownerSignal, ?betaCallsInfoId, ?globalOwnerChangedListId) &*&
                growing_list(betaCallsInfoId, ?betaCallsInfo) &*&
                [1/2]cohort->betaCallsInfo |-> betaCallsInfo &*&
                growing_list(globalOwnerChangedListId, ?globalOwnerChangedList) &*&
                length(betaCallsInfo) == 0 ?
                    length(globalOwnerChangedList) == 0 &*&
                    signal(ownerSignal, L, false)
                :
                    forall_int((beta_calls_info_decreases)(betaCallsInfo)) == true &*&
                    forall_int((global_owner_changed_ok)(betaCallsInfo, globalOwnerChangedList)) == true &*&
                    nth(length(betaCallsInfo) - 1, betaCallsInfo) == beta_call_info(?globalOwner, ?M, ?signal, ?roundsInfoHandleId) &*&
                    has_at<global_round_info>(roundsInfoHandleId, roundsInfoId, globalOwner, _) &*& // Just to prove that the global lock was held at the time of the beta call.
                    length(M) == ticketlock_M_nb_dims &*&
                    signal(signal, L, false) &*&
                    length(globalOwnerChangedList) == length(betaCallsInfo) - 1 ?
                        true
                    :
                        length(globalOwnerChangedList) == length(betaCallsInfo) &*&
                        nth(length(globalOwnerChangedList) - 1, globalOwnerChangedList) == true &*&
                        global_owner_changed_handle(?globalOwnerChangedHandle) &*&
                        is_lower_bound(globalOwnerChangedHandle, ownerIncrBox, globalOwner + 1)
            :
                signal(nth(owner, releaseSignals), L, false)
        :
            [globalLockFrac]ticketlock(globalLock, cohortlock_ticketlock_inv(lock));

predicate_ctor cohort_ticketlock_inv(cohort cohort)(int owner, bool held) =
    [1/2]cohort->owner |-> owner &*&
    [1/2]cohort->held |-> held;

predicate cohortlock(cohortlock lock; predicate(int, bool) inv) =
    malloc_block_cohortlock(lock) &*&
    lock->inv_ |-> inv &*&
    lock->lock |-> ?ticketlock &*& ticketlock(ticketlock, cohortlock_ticketlock_inv(lock)) &*&
    lock->ownerIncrBox |-> ?ownerIncrBox &*&
    lock->roundsInfoId |-> ?roundsInfoId &*&
    atomic_space(create_cohortlock, cohortlock_inv(lock, inv, ownerIncrBox, roundsInfoId));

#define COHORT_INV cohort_inv(cohort, lock, inv, globalLock, frac, ownerIncrBox, roundsInfoId, enqueueIncrBoxId, queueListId, waiteeListId, ownerSignalsId, globalOwnersId, releaseSignalsId)

predicate cohort(cohort cohort; cohortlock lock, predicate(int, bool) inv, real frac) =
    malloc_block_cohort(cohort) &*&
    pointer_within_limits(&cohort->queueSize) == true &*&
    cohort->lockFrac |-> frac &*&
    cohort->cohortlock |-> lock &*&
    cohort->enqueueIncrBoxId |-> ?enqueueIncrBoxId &*&
    cohort->queueListId |-> ?queueListId &*&
    cohort->waiteeListId |-> ?waiteeListId &*&
    cohort->ownerSignalsId |-> ?ownerSignalsId &*&
    cohort->globalOwnersId |-> ?globalOwnersId &*&
    cohort->releaseSignalsId |-> ?releaseSignalsId &*&
    [frac]malloc_block_cohortlock(lock) &*&
    [frac]lock->inv_ |-> inv &*& 
    [frac]lock->lock |-> ?globalLock &*&
    [frac]lock->ownerIncrBox |-> ?ownerIncrBox &*&
    [frac]lock->roundsInfoId |-> ?roundsInfoId &*&
    atomic_space(create_cohort, COHORT_INV) &*&
    cohort->lock |-> ?ticketlock &*& ticketlock(ticketlock, cohort_ticketlock_inv(cohort));

predicate cohortlock_held(cohort cohort, cohortlock lock, predicate(int, bool) inv, real frac, real f, int ticket) =
    [f]malloc_block_cohort(cohort) &*&
    pointer_within_limits(&cohort->queueSize) == true &*&
    [f]cohort->lockFrac |-> frac &*&
    [f]cohort->cohortlock |-> lock &*&
    [f]cohort->enqueueIncrBoxId |-> ?enqueueIncrBoxId &*&
    [f]cohort->queueListId |-> ?queueListId &*&
    [f]cohort->waiteeListId |-> ?waiteeListId &*&
    [f]cohort->ownerSignalsId |-> ?ownerSignalsId &*&
    [f]cohort->globalOwnersId |-> ?globalOwnersId &*&
    [f]cohort->releaseSignalsId |-> ?releaseSignalsId &*&
    [f*frac]malloc_block_cohortlock(lock) &*&
    [f*frac]lock->inv_ |-> inv &*&
    [f*frac]lock->lock |-> ?globalLock &*&
    [f*frac]lock->ownerIncrBox |-> ?ownerIncrBox &*&
    [f*frac]lock->roundsInfoId |-> ?roundsInfoId &*&
    [f]atomic_space(create_cohort, COHORT_INV) &*&
    [1/4]cohort->_passing |-> true &*&
    [1/4]cohort->_passedCount |-> ?passCount &*&
    [1/8]cohort->held |-> true &*&
    [1/8]cohort->owner |-> ?localTicket &*&
    cohort->passing |-> _ &*&
    cohort->passedCount |-> passCount &*&
    [1/2]cohort->queueSizeExcess |-> 0 &*&
    [1/2]cohort->releasing |-> false &*&
    [f]cohort->lock |-> ?ticketlock &*& ticketlock_held(ticketlock, cohort_ticketlock_inv(cohort), f, localTicket) &*&
    has_at(_, globalOwnersId, localTicket, ?globalTicket) &*&
    ticketlock_held(globalLock, cohortlock_ticketlock_inv(lock), frac, globalTicket) &*&
    has_at(_, roundsInfoId, globalTicket, global_round_info(cohort, enqueueIncrBoxId, queueListId, waiteeListId, ?incrBoxId, ?cohortHeldIncrBoxId, ?initialClientOwner, ?initialLocalOwner)) &*&
    ticket == initialClientOwner + passCount &*&
    localTicket == initialLocalOwner + passCount;

@*/

cohortlock create_cohortlock()
//@ requires exists<predicate(int, bool)>(?inv) &*& inv(0, false);
//@ ensures cohortlock(result, inv);
//@ terminates;
{
  //@ open exists(inv);
  cohortlock result = malloc(sizeof(struct cohortlock));
  if (result == 0) abort();
  //@ result->inv_ = inv;
  //@ result->owner = 0;
  //@ result->held_ = false;
  //@ close cohortlock_ticketlock_inv(result)(0, false);
  //@ close exists(cohortlock_ticketlock_inv(result));
  ticketlock lock = create_ticketlock();
  result->lock = lock;
  //@ create_box ownerIncrBox = incr_box(0);
  //@ result->ownerIncrBox = ownerIncrBox;
  //@ box roundsInfoId = create_growing_list();
  //@ result->roundsInfoId = roundsInfoId;
  //@ close cohortlock_inv(result, inv, ownerIncrBox, roundsInfoId)();
  //@ create_atomic_space(create_cohortlock, cohortlock_inv(result, inv, ownerIncrBox, roundsInfoId));
  return result;
}

cohort create_cohort(cohortlock lock)
//@ requires [?frac]cohortlock(lock, ?inv);
//@ ensures cohort(result, lock, inv, frac);
//@ terminates;
{
  cohort cohort = malloc(sizeof(struct cohort));
  if (cohort == 0) abort();
  //@ cohort->lockFrac = frac;
  cohort->cohortlock = lock;
  cohort->queueSize = 0;
  //@ cohort->queueSizeExcess = 0;
  cohort->passing = false;
  //@ cohort->_passing = false;
  cohort->passedCount = 0;
  //@ cohort->_passedCount = 0;
  //@ cohort->releasing = false;
  //@ create_counter(&cohort->queueSize);
  //@ create_box enqueueIncrBoxId = incr_box(0);
  //@ cohort->enqueueIncrBoxId = enqueueIncrBoxId;
  //@ int queueListId = create_ghost_list<pair<void *, real> >();
  //@ cohort->queueListId = queueListId;
  //@ box waiteeListId = create_growing_list();
  //@ cohort->waiteeListId = waiteeListId;
  //@ box ownerSignalsId = create_growing_list<owner_signal_info>();
  //@ cohort->ownerSignalsId = ownerSignalsId;
  //@ box globalOwnersId = create_growing_list<int>();
  //@ cohort->globalOwnersId = globalOwnersId;
  //@ box releaseSignalsId = create_growing_list<void *>();
  //@ cohort->releaseSignalsId = releaseSignalsId;
  //@ cohort->owner = 0;
  //@ cohort->held = false;
  //@ close cohort_ticketlock_inv(cohort)(0, false);
  //@ close exists(cohort_ticketlock_inv(cohort));
  ticketlock ticketlock = create_ticketlock();
  cohort->lock = ticketlock;
  //@ close foreach({}, signal_pred(cohort));
  //@ open cohortlock(lock, inv);
  //@ ticketlock globalLock = lock->lock;
  //@ box ownerIncrBox = lock->ownerIncrBox;
  //@ box roundsInfoId = lock->roundsInfoId;
  //@ close queue_info(cohort, enqueueIncrBoxId, queueListId, waiteeListId, 0, false, false);
  //@ close COHORT_INV();
  //@ create_atomic_space(create_cohort, COHORT_INV);
  return cohort;
}

void cohortlock_acquire(cohort cohort)
/*@
requires
    [?f]cohort(cohort, ?lock, ?inv, ?frac) &*&
    obs(?p, ?obs) &*& forall(map(snd, obs), (func_lt_level)(cohortlock_acquire)) == true &*&
    is_cohortlock_wait_ghost_op(?wop, inv, ?wait_inv, currentThread) &*&
    is_cohortlock_acquire_ghost_op(?aop, inv, wait_inv, ?post, currentThread) &*&
    wait_inv(-1, _, p, obs);
@*/
//@ ensures cohortlock_held(cohort, lock, inv, frac, f, ?ticket) &*& post(ticket);
//@ terminates;
{
  //@ int acquireThread = currentThread;
  //@ open cohort(cohort, lock, inv, frac);
  //@ ticketlock globalLock = lock->lock;
  //@ box ownerIncrBox = lock->ownerIncrBox;
  //@ box roundsInfoId = lock->roundsInfoId;
  //@ box enqueueIncrBoxId = cohort->enqueueIncrBoxId;
  //@ int queueListId = cohort->queueListId;
  //@ box waiteeListId = cohort->waiteeListId;
  //@ box ownerSignalsId = cohort->ownerSignalsId;
  //@ box globalOwnersId = cohort->globalOwnersId;
  //@ box releaseSignalsId = cohort->releaseSignalsId;
  //@ void *initialSignal = create_signal();
  //@ init_signal(initialSignal, L);
  {
    /*@
    predicate pre_() =
        signal(initialSignal, L, false) &*&
        [f/2]cohort->queueListId |-> _ &*&
        [f]atomic_space(create_cohort, COHORT_INV);
    predicate post_() =
        ghost_list_member_handle(queueListId, pair(initialSignal, f)) &*&
        [f]atomic_space(create_cohort, COHORT_INV);
    @*/
    /*@
    produce_lemma_function_pointer_chunk atomic_increment_counter_ghost_op(&cohort->queueSize, pre_, post_, currentThread)() {
        open pre_();
        open_atomic_space(create_cohort, COHORT_INV);
        open COHORT_INV();
        if (cohort->_passing) {
            open_atomic_space(create_cohortlock, cohortlock_inv(lock, inv, ownerIncrBox, roundsInfoId));
            open cohortlock_inv(lock, inv, ownerIncrBox, roundsInfoId)();
            match_has_at(roundsInfoId);
            merge_fractions cohort_owner(cohort, _);
            merge_fractions cohort_held(cohort, _);
        }
        open queue_info(cohort, enqueueIncrBoxId, queueListId, waiteeListId, ?owner, ?held, ?passing);
        
        assert is_atomic_increment_counter_op(?op, &cohort->queueSize, ?P, ?Q);
        op();
        leak is_atomic_increment_counter_op(op, &cohort->queueSize, P, Q);
        
        assert ghost_list(queueListId, ?queue);
        ghost_list_insert(queueListId, {}, queue, pair(initialSignal, f));
        close signal_pred(cohort)(pair(initialSignal, f));
        close foreach(cons(pair(initialSignal, f), queue), signal_pred(cohort));
        
        assert growing_list<void *>(waiteeListId, ?waitees);
        if (length(waitees) == owner) {
            growing_list_add(waiteeListId, initialSignal);
            nth_append_r(waitees, {initialSignal}, 0);
        }
        
        consuming_box_predicate incr_box(enqueueIncrBoxId, ?nbEnqueues)
        perform_action incr() {}
        producing_box_predicate incr_box(nbEnqueues + 1);
        
        close queue_info(cohort, enqueueIncrBoxId, queueListId, waiteeListId, owner, held, passing);
        if (cohort->_passing) {
            close cohortlock_inv(lock, inv, ownerIncrBox, roundsInfoId)();
            close_atomic_space(create_cohortlock, cohortlock_inv(lock, inv, ownerIncrBox, roundsInfoId));
        }
        
        close COHORT_INV();
        close_atomic_space(create_cohort, COHORT_INV);
        close post_();
    };
    @*/
    //@ close pre_();
    atomic_increment_counter(&cohort->queueSize);
    //@ open post_();
  }
  //@ produce_func_lt(ticketlock_acquire);
  //@ produce_func_lt(ticketlock_dispose);
  /*@
  if (!forall(map(snd, obs), (func_lt_level)(ticketlock_acquire))) {
      level badLevel = not_forall(map(snd, obs), (func_lt_level)(ticketlock_acquire));
      forall_elim(map(snd, obs), (func_lt_level)(cohortlock_acquire), badLevel);
      assert false;
  }
  @*/
  {
    /*@
    predicate nb_beta_calls_seen(int nbBetaCallsSeen) = true;
    predicate post_beta_call_info(handle globalOwnerSeenHandleId, bool cohortLockWasHeld) = true;
    predicate global_owner_seen_info_handle_id(handle globalOwnerSeenInfoHandleId, handle passCountHandleId) = true;
    predicate cohort_held_handle_id(handle cohortHeldHandleId) = true;
    predicate wait_inv_global_owner_changed_handle(handle waitInvGlobalOwnerChangedHandle) = true;
    predicate wait_inv_holding_global_lock_info(handle globalOwnerHandle, handle passCountHandle) = true;
    predicate wait_inv_(int oldOwner, list<int> oldM, list<pathcomp> oldp, list<pair<void *, level> > oldObs) =
        wait_inv(?oldClientOwner, ?oldClientM, ?oldClientPath, ?oldClientObs) &*& is_ancestor_of(oldClientPath, oldp) == true &*&
        is_cohortlock_wait_ghost_op(wop, inv, wait_inv, currentThread) &*& forall(map(snd, oldClientObs), (func_lt_level)(cohortlock_acquire)) == true &*&
        is_cohortlock_acquire_ghost_op(aop, inv, wait_inv, post, currentThread) &*&
        ghost_list_member_handle<pair<void *, real> >(queueListId, pair(?mySignal, f)) &*&
        oldObs == cons(pair(mySignal, L), oldClientObs) &*&
        [f]atomic_space(create_cohort, COHORT_INV) &*&
        oldOwner == -1 ?
            oldClientOwner == -1 &*&
            call_below_perm_(currentThread, cohortlock_acquire)
        :
            length(oldM) == ticketlock_M_nb_dims &*&
            exists(pair(?waitingForGlobalLock, ?holdingGlobalLock)) &*&
            waitingForGlobalLock ?
                !holdingGlobalLock &*&
                has_at(_, ownerSignalsId, oldOwner, owner_signal_info(?ownerSignal, ?betaCallsInfoId, ?globalOwnerChangedListId)) &*&
                nb_beta_calls_seen(?nbBetaCallsSeen) &*& 0 <= nbBetaCallsSeen &*&
                nbBetaCallsSeen == 0 ?
                    oldClientOwner == -1 || lexprod_lt(cons(1, append(oldM, cons(3, zeros(ticketlock_M_nb_dims + 1)))), oldClientM) &*&
                    call_below_perm_lex(?pp, cohortlock_acquire, append(oldM, cons(3, zeros(ticketlock_M_nb_dims + 1)))) &*&
                    wait_perm(pp, ownerSignal, L, ticketlock_acquire) &*& is_ancestor_of(pp, oldp) == true
                :
                    post_beta_call_info(?globalOwnerSeenHandleId, ?cohortLockWasHeld) &*&
                    has_at(_, betaCallsInfoId, nbBetaCallsSeen - 1, beta_call_info(?betaCallGlobalOwner, ?globalM, ?signal, _)) &*&
                    length(globalM) == ticketlock_M_nb_dims &*&
                    is_lower_bound(globalOwnerSeenHandleId, ownerIncrBox, ?globalOwnerSeen) &*&
                    globalOwnerSeen == betaCallGlobalOwner ?
                        global_owner_seen_info_handle_id(?globalOwnerInfoHandleId, ?passCountHandleId) &*&
                        has_at(globalOwnerInfoHandleId, roundsInfoId, globalOwnerSeen, global_round_info(?ownerCohort, ?ownerEnqueueIncrBoxId, ?ownerQueueListId, ?ownerWaiteeListId, ?ownerIncrBoxId, ?ownerCohortHeldIncrBoxId, ?initialClientOwner, ?initialLocalOwner)) &*&
                        is_lower_bound(passCountHandleId, ownerIncrBoxId, ?passCount) &*& 0 <= passCount &*& passCount <= MAX_PASS_COUNT &*&
                        call_below_perm_lex(?pp, cohortlock_acquire, append(oldM, cons(2, append(globalM, {MAX_PASS_COUNT - passCount + 1})))) &*&
                        is_ancestor_of(pp, oldp) == true &*&
                        !cohortLockWasHeld ?
                            oldClientOwner == -1 || lexprod_lt(cons(1, append(oldM, cons(2, append(globalM, {MAX_PASS_COUNT - passCount + 1})))), oldClientM) &*&
                            has_at(_, ownerWaiteeListId, initialLocalOwner + passCount, ?waiteeSignal) &*&
                            wait_perm(pp, waiteeSignal, L, ticketlock_acquire)
                        :
                            cohort_held_handle_id(?cohortHeldHandleId) &*&
                            is_lower_bound(cohortHeldHandleId, ownerCohortHeldIncrBoxId, passCount + 1) &*&
                            oldClientOwner == initialClientOwner + passCount &*&
                            oldClientM == cons(1, append(oldM, cons(2, append(globalM, {MAX_PASS_COUNT - passCount + 1}))))
                    :   
                        globalOwnerSeen > betaCallGlobalOwner &*&
                        wait_inv_global_owner_changed_handle(?waitInvGlobalOwnerChangedHandle) &*&
                        has_at(waitInvGlobalOwnerChangedHandle, globalOwnerChangedListId, nbBetaCallsSeen - 1, true) &*&
                        oldClientOwner == -1 || lexprod_lt(cons(1, append(oldM, cons(2, append(globalM, {0})))), oldClientM) &*&
                        call_below_perm_lex(?pp, cohortlock_acquire, append(oldM, cons(2, append(globalM, {0})))) &*&
                        wait_perm(pp, signal, L, ticketlock_acquire) &*& is_ancestor_of(pp, oldp) == true
            :
                holdingGlobalLock ?
                    call_below_perm_lex(?pp, cohortlock_acquire, append(oldM, cons(1, zeros(ticketlock_M_nb_dims + 1)))) &*&
                    is_ancestor_of(pp, oldp) == true &*&
                    has_at(_, globalOwnersId, oldOwner, ?globalOwner) &*&
                    wait_inv_holding_global_lock_info(?globalOwnerHandle, ?passCountHandleId) &*&
                    has_at(globalOwnerHandle, roundsInfoId, globalOwner, global_round_info(cohort, enqueueIncrBoxId, queueListId, waiteeListId, ?incrBoxId, ?cohortHeldIncrBoxId, ?initialClientOwner, ?initialLocalOwner)) &*&
                    is_lower_bound(passCountHandleId, incrBoxId, ?passedCount) &*&
                    oldClientM == cons(1, append(oldM, cons(1, zeros(ticketlock_M_nb_dims + 1)))) &*&
                    oldClientOwner == initialClientOwner + passedCount &*&
                    oldOwner == initialLocalOwner + passedCount
                :
                    has_at(_, releaseSignalsId, oldOwner, ?releaseSignal) &*&
                    oldClientOwner == -1 || lexprod_lt(cons(1, append(oldM, cons(0, zeros(ticketlock_M_nb_dims + 1)))), oldClientM) &*&
                    call_below_perm_lex(?pp, cohortlock_acquire, append(oldM, cons(0, zeros(ticketlock_M_nb_dims + 1)))) &*&
                    wait_perm(pp, releaseSignal, L, ticketlock_acquire) &*& is_ancestor_of(pp, oldp) == true;                    
    predicate post_(int ticket) =
        [f/2]cohort->queueListId |-> _ &*&
        [f]atomic_space(create_cohort, COHORT_INV) &*&
        cohort->passing |-> ?passing &*&
        cohort->passedCount |-> ?passedCount &*&
        [1/4]cohort->_passing |-> passing &*&
        [1/4]cohort->_passedCount |-> passedCount &*&
        [1/8]cohort->owner |-> ticket &*&
        [1/8]cohort->held |-> true &*&
        [1/2]cohort->queueSizeExcess |-> 1 &*&
        [1/2]cohort->releasing |-> false &*&
        passing ?
            ticketlock_held(globalLock, cohortlock_ticketlock_inv(lock), frac, ?globalTicket) &*&
            has_at(_, roundsInfoId, globalTicket, global_round_info(cohort, enqueueIncrBoxId, queueListId, waiteeListId, ?incrBoxId, ?cohortHeldIncrBoxId, ?initialClientOwner, ?initialLocalOwner)) &*&
            ticket == initialLocalOwner + passedCount &*&
            post(initialClientOwner + passedCount) &*&
            has_at(_, globalOwnersId, ticket, globalTicket)
        :
            passedCount == 0 &*&
            [frac]ticketlock(globalLock, cohortlock_ticketlock_inv(lock)) &*&
            wait_inv(?clientOwner, ?clientM, ?clientPhase, ?clientObs) &*& forall(map(snd, clientObs), (func_lt_level)(cohortlock_acquire)) == true &*&
            clientOwner == -1 || lexprod_lt(cons(0, cons(1, zeros(2*ticketlock_M_nb_dims + 1))), clientM) &*&
            is_cohortlock_wait_ghost_op(wop, inv, wait_inv, currentThread) &*&
            is_cohortlock_acquire_ghost_op(aop, inv, wait_inv, post, currentThread) &*&
            has_at(_, ownerSignalsId, ticket, owner_signal_info(?ownerSignal, ?betaCallsInfoId, ?globalOwnerChangedListId)) &*&
            [1/2]cohort->betaCallsInfo |-> {} &*&
            obs(?p1, cons(pair(ownerSignal, L), clientObs)) &*& is_ancestor_of(clientPhase, p1) == true;
    @*/
    /*@
    produce_lemma_function_pointer_chunk ticketlock_wait_ghost_op(cohort_ticketlock_inv(cohort), wait_inv_, currentThread)(M) {
        open wait_inv_(?oldOwner, ?oldM, ?oldp, ?oldObs);
        assert obs(?p1, oldObs);
        assert wait_inv(?oldClientOwner, ?oldClientM, ?oldClientP, ?oldClientObs);
        is_ancestor_of_trans(oldClientP, oldp, p1);
        is_ancestor_of_refl(p1);
        assert ghost_list_member_handle<pair<void *, real> >(queueListId, pair(?mySignal, f));
        open cohort_ticketlock_inv(cohort)(?owner, true);
        
        // First, set our signal so that we can call client beta without holding any internal obligations.
        assert atomic_spaces(?spaces);
        if (mem(pair(create_cohort, COHORT_INV), spaces)) {
            mem_map(pair(create_cohort, COHORT_INV), spaces, fst);
            forall_elim(map(fst, spaces), (func_gt)(ticketlock_dispose), create_cohort);
            assert false;
        }
        open_atomic_space(create_cohort, COHORT_INV);
        open COHORT_INV();
        if (mem(pair(create_cohortlock, cohortlock_inv(lock, inv, ownerIncrBox, roundsInfoId)), spaces)) {
            mem_map(pair(create_cohortlock, cohortlock_inv(lock, inv, ownerIncrBox, roundsInfoId)), spaces, fst);
            forall_elim(map(fst, spaces), (func_gt)(ticketlock_dispose), create_cohortlock);
            assert false;
        }
        open_atomic_space(create_cohortlock, cohortlock_inv(lock, inv, ownerIncrBox, roundsInfoId));
        open cohortlock_inv(lock, inv, ownerIncrBox, roundsInfoId)();
        if (cohort->_passing) {
            match_has_at(roundsInfoId);
            merge_fractions cohort_owner(cohort, _);
            merge_fractions cohort_held(cohort, _);
        }
        int globalOwner = lock->owner;
        assert growing_list<global_round_info>(roundsInfoId, ?roundsInfo);
        open queue_info(cohort, enqueueIncrBoxId, queueListId, waiteeListId, owner, true, ?passing);
        
        assert ghost_list(queueListId, ?queue);
        ghost_list_remove_remove(queueListId, pair(mySignal, f));
        foreach_remove(pair(mySignal, f), queue);
        open signal_pred(cohort)(pair(mySignal, f));
        set_signal(mySignal);
        leak signal(mySignal, L, true);
        
        if (!forall(map(fst, spaces), (func_gt)(cohortlock_dispose))) {
            void *badFunc = not_forall(map(fst, spaces), (func_gt)(cohortlock_dispose));
            forall_elim(map(fst, spaces), (func_gt)(ticketlock_dispose), badFunc);
            assert false;
        }
        
        if (!forall(map(snd, oldClientObs), (level_lt)(L))) {
            level badLevel = not_forall(map(snd, oldClientObs), (level_lt)(L));
            forall_elim(map(snd, oldClientObs), (func_lt_level)(cohortlock_acquire), badLevel);
            assert false;
        }
        
        if (!forall(map(snd, oldClientObs), (func_lt_level)(ticketlock_acquire))) {
            level badLevel = not_forall(map(snd, oldClientObs), (func_lt_level)(ticketlock_acquire));
            forall_elim(map(snd, oldClientObs), (func_lt_level)(cohortlock_acquire), badLevel);
            assert false;
        }
        
        if (oldOwner == -1) {
            pathize_call_below_perm__lex(append(M, cons(4, zeros(ticketlock_M_nb_dims + 1))));
            leak call_below_perm(p1, cohortlock_acquire);
        } else if (lexprod_lt(M, oldM)) {
            open exists(pair(?wasWaitingForGlobalLock, ?wasHoldingGlobalLock));
            list<int> oldDegree;
            if (wasWaitingForGlobalLock) {
                leak has_at(_, ownerSignalsId, oldOwner, owner_signal_info(?ownerSignal, ?betaCallsInfoId, ?globalOwnerChangedListId));
                open nb_beta_calls_seen(?nbBetaCallsSeen);
                if (nbBetaCallsSeen == 0) {
                    oldDegree = cons(3, zeros(ticketlock_M_nb_dims + 1));
                    leak wait_perm(?pp, ownerSignal, L, ticketlock_acquire);
                } else {
                    open post_beta_call_info(?globalOwnerSeenHandleId, ?cohortLockWasHeld);
                    leak is_lower_bound(globalOwnerSeenHandleId, ownerIncrBox, ?globalOwnerSeen);
                    leak has_at<beta_call_info>(_, betaCallsInfoId, nbBetaCallsSeen - 1, beta_call_info(?betaCallGlobalOwner, ?globalM, ?signal, _));
                    if (globalOwnerSeen == betaCallGlobalOwner) {
                        open global_owner_seen_info_handle_id(?globalOwnerSeenInfoHandleId, ?passCountHandleId);
                        leak has_at<global_round_info>(globalOwnerSeenInfoHandleId, roundsInfoId, globalOwnerSeen, global_round_info(?ownerCohort, ?ownerEnqueueIncrBoxId, ?ownerQueueListId, ?ownerWaiteeListId, ?ownerIncrBoxId, ?ownerCohortHeldIncrBoxId, ?initialClientOwner, ?initialLocalOwner));
                        leak is_lower_bound(passCountHandleId, ownerIncrBoxId, ?passCount);
                        oldDegree = cons(2, append(globalM, {MAX_PASS_COUNT - passCount + 1}));
                        if (!cohortLockWasHeld) {
                            leak has_at<void *>(_, ownerWaiteeListId, _, ?waiteeSignal);
                            leak wait_perm(?pp, waiteeSignal, _, _);
                        } else {
                            open cohort_held_handle_id(?cohortHeldHandleId);
                            leak is_lower_bound(cohortHeldHandleId, ownerCohortHeldIncrBoxId, _);
                        }
                    } else {
                        oldDegree = cons(2, append(globalM, {0}));
                        open wait_inv_global_owner_changed_handle(?waitInvGlobalOwnerChangedHandle);
                        leak has_at<bool>(waitInvGlobalOwnerChangedHandle, _, _, _);
                        leak wait_perm(_, signal, L, ticketlock_acquire);
                    }
                }
            } else if (wasHoldingGlobalLock) {
                oldDegree = cons(1, zeros(ticketlock_M_nb_dims + 1));
                leak has_at<int>(_, globalOwnersId, oldOwner, ?oldGlobalOwner);
                open wait_inv_holding_global_lock_info(?globalOwnerHandle, ?passCountHandleId);
                leak has_at<global_round_info>(globalOwnerHandle, roundsInfoId, oldGlobalOwner, global_round_info(cohort, enqueueIncrBoxId, queueListId, waiteeListId, ?incrBoxId, ?cohortHeldIncrBoxId, ?initialClientOwner, ?initialLocalOwner));
                leak is_lower_bound(passCountHandleId, incrBoxId, ?passedCount);
            } else {
                oldDegree = cons(0, zeros(ticketlock_M_nb_dims + 1));
                leak has_at<void *>(_, releaseSignalsId, oldOwner, ?releaseSignal);
                leak wait_perm(_, releaseSignal, _, _);
            }
            lexprod_lt_append_l(
                M, cons(4, zeros(ticketlock_M_nb_dims + 1)),
                oldM, oldDegree);
            if (oldClientOwner != -1 && lexprod_lt(cons(1, append(oldM, oldDegree)), oldClientM))
                lexprod_lt_trans(
                    cons(1, append(M, cons(4, zeros(ticketlock_M_nb_dims + 1)))),
                    cons(1, append(oldM, oldDegree)),
                    oldClientM);
            call_below_perm_lex_weaken(append(M, cons(4, zeros(ticketlock_M_nb_dims + 1))));
            leak call_below_perm(?pp, _);
            is_ancestor_of_trans(pp, oldp, p1);
        }
        
        bool wasWaitingForGlobalLock = false;
        bool wasHoldingGlobalLock = false;
        if (oldOwner != -1 && !lexprod_lt(M, oldM)) {
            open exists(pair(?wasWaitingForGlobalLock_, ?wasHoldingGlobalLock_));
            wasWaitingForGlobalLock = wasWaitingForGlobalLock_;
            wasHoldingGlobalLock = wasHoldingGlobalLock_;
        }
        
        close exists(pair(!cohort->_passing && !cohort->releasing, cohort->_passing));
        list<int> oldDegree = cons(4, zeros(ticketlock_M_nb_dims + 1));
        if (!cohort->_passing && !cohort->releasing) {
            if (oldOwner != -1 && !lexprod_lt(M, oldM) && !wasWaitingForGlobalLock) {
                if (wasHoldingGlobalLock) {
                    match_has_at<int>(globalOwnersId);
                    assert false;
                } else {
                    match_has_at<void *>(releaseSignalsId);
                    assert false;
                }
            }
            int nbBetaCallsSeen = 0;
            if (oldOwner != -1 && !lexprod_lt(M, oldM)) {
                match_has_at<owner_signal_info>(ownerSignalsId);
                leak has_at<owner_signal_info>(_, ownerSignalsId, _, _);
                open nb_beta_calls_seen(?nbBetaCallsSeen_);
                nbBetaCallsSeen = nbBetaCallsSeen_;
            }
            
            assert growing_list<owner_signal_info>(ownerSignalsId, ?ownerSignals);
            assert nth(owner, ownerSignals) == owner_signal_info(?ownerSignal, ?betaCallsInfoId, ?globalOwnerChangedListId);
            assert growing_list<beta_call_info>(betaCallsInfoId, ?betaCallsInfo);
            assert growing_list<bool>(globalOwnerChangedListId, ?globalOwnerChangedList);
            
            close nb_beta_calls_seen(length(betaCallsInfo));
            create_has_at<owner_signal_info>(ownerSignalsId, owner);
            
            if (length(betaCallsInfo) == 0) {
                if (oldOwner == -1 || lexprod_lt(M, oldM)) {
                    lexprod_lt_append_r(M,
                        cons(3, zeros(ticketlock_M_nb_dims + 1)),
                        cons(4, zeros(ticketlock_M_nb_dims + 1)));
                    if (oldClientOwner != -1)
                        lexprod_lt_trans(
                            cons(1, append(M, cons(3, zeros(ticketlock_M_nb_dims + 1)))),
                            cons(1, append(M, cons(4, zeros(ticketlock_M_nb_dims + 1)))),
                            oldClientM);
                    call_below_perm_lex_weaken(append(M, cons(3, zeros(ticketlock_M_nb_dims + 1))));
                    create_wait_perm(ownerSignal, L, ticketlock_acquire);
                } else {
                    if (nbBetaCallsSeen > 0) {
                        match_has_at<beta_call_info>(betaCallsInfoId);
                        assert false;
                    }
                    assert wait_perm(?pp, _, _, _);
                    is_ancestor_of_trans(pp, oldp, p1);
                }
                close exists(pair(0, pair(0, false)));
                wait(ownerSignal);
            } else {
                assert nth(length(betaCallsInfo) - 1, betaCallsInfo) == beta_call_info(?betaCallGlobalOwner, ?globalM, ?signal, ?roundsInfoHandleId);
                assert has_at<global_round_info>(roundsInfoHandleId, roundsInfoId, betaCallGlobalOwner, global_round_info(?ownerCohort, ?ownerEnqueueIncrBoxId, ?ownerQueueListId, ?ownerWaiteeListId, ?ownerIncrBoxId, ?ownerCohortHeldIncrBoxId, ?initialClientOwner, ?initialLocalOwner));
                match_has_at_<global_round_info>(roundsInfoHandleId);
                int globalOwnerSeen;
                bool cohortLockWasHeld;
                bool sameGlobalM = false;
                if (oldOwner != -1 && !lexprod_lt(M, oldM)){
                    assert call_below_perm_lex(?pp, _, _);
                    is_ancestor_of_trans(pp, oldp, p1);
                    if (nbBetaCallsSeen == 0) {
                        oldDegree = cons(3, zeros(ticketlock_M_nb_dims + 1));
                        leak wait_perm(_, ownerSignal, _, _);
                    } else {
                        open post_beta_call_info(?globalOwnerSeenHandleId, ?cohortLockWasHeld_);
                        consuming_box_predicate incr_box(ownerIncrBox, globalOwner)
                        consuming_handle_predicate is_lower_bound(globalOwnerSeenHandleId, ?globalOwnerSeen_)
                        perform_action noop() {};
                        globalOwnerSeen = globalOwnerSeen_;
                        cohortLockWasHeld = cohortLockWasHeld_;
                        match_has_at<beta_call_info>(betaCallsInfoId);
                        leak has_at(_, betaCallsInfoId, nbBetaCallsSeen - 1, beta_call_info(?oldBetaCallGlobalOwner, ?oldGlobalM, ?oldSignal, _));
                        if (nbBetaCallsSeen < length(betaCallsInfo))
                            beta_calls_info_mono(betaCallsInfo, nbBetaCallsSeen - 1, length(betaCallsInfo) - 1);
                        if (lexprod_lt(globalM, oldGlobalM)) {
                            list<int> oldSubdegree;
                            if (globalOwnerSeen == oldBetaCallGlobalOwner) {
                                open global_owner_seen_info_handle_id(?globalOwnerSeenInfoHandleId, ?passCountHandleId);
                                match_has_at_<global_round_info>(globalOwnerSeenInfoHandleId);
                                leak has_at(globalOwnerSeenInfoHandleId, _, globalOwnerSeen_, global_round_info(?oldOwnerCohort, ?oldOwnerEnqueueIncrBoxId, ?oldOwnerQueueListId, ?oldOwnerWaiteeListId, ?oldOwnerIncrBoxId, ?oldOwnerCohortHeldIncrBoxId, ?oldInitialClientOwner, ?oldInitialLocalOwner));
                                leak is_lower_bound(passCountHandleId, oldOwnerIncrBoxId, ?passCount);
                                oldSubdegree = {MAX_PASS_COUNT - passCount + 1};
                                if (!cohortLockWasHeld) {
                                    leak has_at<void *>(_, oldOwnerWaiteeListId, _, ?waiteeSignal);
                                    leak wait_perm(_, waiteeSignal, _, _);
                                } else {
                                    open cohort_held_handle_id(?cohortHeldHandleId);
                                    leak is_lower_bound(cohortHeldHandleId, oldOwnerCohortHeldIncrBoxId, _);
                                }
                            } else {
                                oldSubdegree = {0};
                                open wait_inv_global_owner_changed_handle(?waitInvGlobalOwnerChangedHandle);
                                leak has_at<bool>(waitInvGlobalOwnerChangedHandle, _, _, _);
                                leak wait_perm(_, oldSignal, L, ticketlock_acquire);
                            }
                            oldDegree = cons(2, append(oldGlobalM, oldSubdegree));
                            lexprod_lt_append_l(
                                globalM, {MAX_PASS_COUNT + 2},
                                oldGlobalM, oldSubdegree);
                        } else
                            sameGlobalM = true;
                    }
                }
                create_has_at<beta_call_info>(betaCallsInfoId, length(betaCallsInfo) - 1);
                consuming_box_predicate incr_box(ownerIncrBox, globalOwner)
                perform_action noop() {}
                producing_fresh_handle_predicate is_lower_bound(globalOwner);
                assert is_lower_bound(?globalOwnerHandleId, ownerIncrBox, globalOwner);
                list<int> oldSubdegree;
                if (!sameGlobalM) {
                    lexprod_lt_append_r(M,
                        cons(2, append(globalM, {MAX_PASS_COUNT + 2})),
                        oldDegree);
                    if (oldClientOwner != -1 && lexprod_lt(cons(1, append(M, oldDegree)), oldClientM))
                        lexprod_lt_trans(
                            cons(1, append(M, cons(2, append(globalM, {MAX_PASS_COUNT + 2})))),
                            cons(1, append(M, oldDegree)),
                            oldClientM);
                    call_below_perm_lex_weaken(append(M, cons(2, append(globalM, {MAX_PASS_COUNT + 2}))));
                    leak call_below_perm(?pp, cohortlock_acquire);
                    oldSubdegree = {MAX_PASS_COUNT + 2};
                }
                if (betaCallGlobalOwner == globalOwner) {
                    handle globalOwnerInfoHandleId = create_has_at<global_round_info>(roundsInfoId, globalOwner);
                    close post_beta_call_info(globalOwnerHandleId, ownerCohort->held);
                    assert [_]lock->held_ |-> true;
                    int passCount = ownerCohort->_passedCount;
                    int oldPassCount;
                    if (sameGlobalM) {
                        open global_owner_seen_info_handle_id(?globalOwnerSeenInfoHandleId, ?oldPassCountHandleId);
                        match_has_at_<global_round_info>(globalOwnerSeenInfoHandleId);
                        leak has_at<global_round_info>(globalOwnerSeenInfoHandleId, _, _, _);
                        consuming_box_predicate incr_box(ownerIncrBoxId, passCount)
                        consuming_handle_predicate is_lower_bound(oldPassCountHandleId, ?oldPassCount_)
                        perform_action noop() {};
                        oldPassCount = oldPassCount_;
                        oldSubdegree = {MAX_PASS_COUNT - oldPassCount + 1};
                        if (oldPassCount < passCount) {
                            assert call_below_perm_lex(?pp, _, _);
                            is_ancestor_of_trans(pp, oldp, p1);
                            if (!cohortLockWasHeld) {
                                leak has_at<void *>(_, ownerWaiteeListId, _, ?waiteeSignal);
                                leak wait_perm(_, waiteeSignal, _, _);
                            } else {
                                open cohort_held_handle_id(?cohortHeldHandleId);
                                leak is_lower_bound(cohortHeldHandleId, _, _);
                            }
                        }
                    }
                    consuming_box_predicate incr_box(ownerIncrBoxId, passCount)
                    perform_action noop() {}
                    producing_fresh_handle_predicate is_lower_bound(passCount);
                    assert is_lower_bound(?passCountHandleId, ownerIncrBoxId, passCount);
                    close global_owner_seen_info_handle_id(globalOwnerInfoHandleId, passCountHandleId);
                    if (!sameGlobalM || oldPassCount < passCount) {
                        lexprod_lt_append_r(globalM, {MAX_PASS_COUNT - passCount + 1}, oldSubdegree);
                        lexprod_lt_append_r(M,
                            cons(2, append(globalM, {MAX_PASS_COUNT - passCount + 1})),
                            cons(2, append(globalM, oldSubdegree)));
                        if (oldClientOwner != -1 && oldClientM != cons(1, append(M, cons(2, append(globalM, oldSubdegree)))))
                            lexprod_lt_trans(
                                cons(1, append(M, cons(2, append(globalM, {MAX_PASS_COUNT - passCount + 1})))),
                                cons(1, append(M, cons(2, append(globalM, oldSubdegree)))),
                                oldClientM);
                        call_below_perm_lex_weaken(append(M, cons(2, append(globalM, {MAX_PASS_COUNT - passCount + 1}))));
                    }
                    if (!ownerCohort->held) {
                        open queue_info(ownerCohort, ownerEnqueueIncrBoxId, ownerQueueListId, ownerWaiteeListId, initialLocalOwner + passCount, false, true);
                        assert ghost_list<pair<void *, real> >(ownerQueueListId, ?ownerQueue);
                        assert growing_list<void *>(ownerWaiteeListId, ?ownerWaitees);
                        void *waiteeSignal = nth(initialLocalOwner + passCount, ownerWaitees);
                        
                        if (!sameGlobalM || oldPassCount < passCount) {
                            create_wait_perm(waiteeSignal, L, ticketlock_acquire);
                            create_has_at<void *>(ownerWaiteeListId, initialLocalOwner + passCount);
                        } else if (cohortLockWasHeld) {
                            open cohort_held_handle_id(?cohortHeldHandleId);
                            consuming_box_predicate incr_box(ownerCohortHeldIncrBoxId, ?cohortHeldCount)
                            consuming_handle_predicate is_lower_bound(cohortHeldHandleId, ?oldCohortHeldCount)
                            perform_action noop() {};
                            assert false;
                        } else {
                            match_has_at(ownerWaiteeListId);
                        }
                        pair<void *, real> queueElem = mem_map_mem(waiteeSignal, ownerQueue, fst);
                        foreach_remove(queueElem, ownerQueue);
                        open signal_pred(ownerCohort)(queueElem);
                        wait(waiteeSignal);
                        close signal_pred(ownerCohort)(queueElem);
                        foreach_unremove(queueElem, ownerQueue);
                        close queue_info(ownerCohort, ownerEnqueueIncrBoxId, ownerQueueListId, ownerWaiteeListId, initialLocalOwner + passCount, false, true);
                    } else {
                        if (!sameGlobalM || oldPassCount < passCount || !cohortLockWasHeld) {
                            if (!sameGlobalM || oldPassCount < passCount) {
                                leak call_below_perm(_, cohortlock_acquire);
                            } else if (!cohortLockWasHeld) {
                                leak has_at<void *>(_, ownerWaiteeListId, _, _);
                                leak wait_perm(_, _, _, _);
                            }
                            consuming_box_predicate incr_box(ownerCohortHeldIncrBoxId, passCount + 1)
                            perform_action noop() {}
                            producing_fresh_handle_predicate is_lower_bound(passCount + 1);
                            assert is_lower_bound(?cohortHeldHandleId, ownerCohortHeldIncrBoxId, passCount + 1);
                            close cohort_held_handle_id(cohortHeldHandleId);
                        }
                        wop(cons(1, append(M, cons(2, append(globalM, {MAX_PASS_COUNT - passCount + 1})))));
                        call_perm__weaken(cohortlock_acquire, ticketlock_acquire);
                    }
                } else {
                    close post_beta_call_info(globalOwnerHandleId, false);
                    if (!sameGlobalM || globalOwnerSeen == betaCallGlobalOwner) {
                        if (sameGlobalM) {
                            open global_owner_seen_info_handle_id(?globalOwnerSeenInfoHandleId, ?passCountHandleId);
                            leak has_at(globalOwnerSeenInfoHandleId, roundsInfoId, globalOwnerSeen, global_round_info(?oldOwnerCohort, ?oldOwnerEnqueueIncrBoxId, ?oldOwnerQueueListId, ?oldOwnerWaiteeListId, ?oldOwnerIncrBoxId, ?oldOwnerCohortHeldIncrBoxId, ?oldInitialClientOwner, ?oldInitialLocalOwner));
                            leak is_lower_bound(passCountHandleId, oldOwnerIncrBoxId, ?passCount);
                            oldSubdegree = {MAX_PASS_COUNT - passCount + 1};
                            assert call_below_perm_lex(?pp, _, _);
                            is_ancestor_of_trans(pp, oldp, p1);
                            if (!cohortLockWasHeld) {
                                leak has_at<void *>(_, oldOwnerWaiteeListId, _, ?waiteeSignal);
                                leak wait_perm(_, waiteeSignal, _, _);
                            } else {
                                open cohort_held_handle_id(?cohortHeldHandleId);
                                leak is_lower_bound(cohortHeldHandleId, _, _);
                            }
                        }
                        lexprod_lt_append_r(globalM, {0}, oldSubdegree);
                        lexprod_lt_append_r(M,
                            cons(2, append(globalM, {0})),
                            cons(2, append(globalM, oldSubdegree)));
                        if (oldClientOwner != -1 && oldClientM != cons(1, append(M, cons(2, append(globalM, oldSubdegree)))))
                            lexprod_lt_trans(
                                cons(1, append(M, cons(2, append(globalM, {0})))),
                                cons(1, append(M, cons(2, append(globalM, oldSubdegree)))),
                                oldClientM);
                        call_below_perm_lex_weaken(append(M, cons(2, append(globalM, {0}))));
                        create_wait_perm(signal, L, ticketlock_acquire);
                        if (length(globalOwnerChangedList) == length(betaCallsInfo) - 1) {
                             growing_list_add<bool>(globalOwnerChangedListId, true);
                             nth_append_r(globalOwnerChangedList, {true}, 0);
                             if (!forall_int((global_owner_changed_ok)(betaCallsInfo, append(globalOwnerChangedList, {true})))) {
                                 int i = not_forall_int((global_owner_changed_ok)(betaCallsInfo, append(globalOwnerChangedList, {true})));
                                 if (i - 1 < length(globalOwnerChangedList)) {
                                     nth_append(globalOwnerChangedList, {true}, i - 1);
                                     forall_int_elim((global_owner_changed_ok)(betaCallsInfo, globalOwnerChangedList), i);
                                     assert false;
                                 }
                                 assert false;
                             }
                             consuming_box_predicate incr_box(ownerIncrBox, globalOwner)
                             perform_action noop() {}
                             producing_fresh_handle_predicate is_lower_bound(betaCallGlobalOwner + 1);
                             assert is_lower_bound(?globalOwnerChangedHandle, ownerIncrBox, betaCallGlobalOwner + 1);
                             close global_owner_changed_handle(globalOwnerChangedHandle);
                        }
                        handle waitInvGlobalOwnerChangedHandle = create_has_at<bool>(globalOwnerChangedListId, length(betaCallsInfo) - 1);
                        close wait_inv_global_owner_changed_handle(waitInvGlobalOwnerChangedHandle);
                    } else if (nbBetaCallsSeen < length(betaCallsInfo)) {
                        predicate foo() = !lexprod_lt(globalM, nth(nbBetaCallsSeen - 1, betaCallsInfo)->M);
                        
                        close foo();
                        note(!lexprod_lt(globalM, nth(nbBetaCallsSeen - 1, betaCallsInfo)->M));
                        open wait_inv_global_owner_changed_handle(?waitInvGlobalOwnerChangedHandle);
                        match_has_at_<bool>(waitInvGlobalOwnerChangedHandle);
                        forall_int_elim((global_owner_changed_ok)(betaCallsInfo, globalOwnerChangedList), nbBetaCallsSeen);
                        forall_int_elim((beta_calls_info_decreases)(betaCallsInfo), nbBetaCallsSeen);
                        assert lexprod_lt(nth(nbBetaCallsSeen, betaCallsInfo)->M, nth(nbBetaCallsSeen - 1, betaCallsInfo)->M) == true;
                        if (nbBetaCallsSeen + 1 < length(betaCallsInfo))
                            beta_calls_info_mono(betaCallsInfo, nbBetaCallsSeen, length(betaCallsInfo) - 1);
                        if (nth(nbBetaCallsSeen, betaCallsInfo)->M != globalM)
                            lexprod_lt_trans(globalM, nth(nbBetaCallsSeen, betaCallsInfo)->M, nth(nbBetaCallsSeen - 1, betaCallsInfo)->M);
                        note(lexprod_lt(globalM, nth(nbBetaCallsSeen - 1, betaCallsInfo)->M));
                        open foo();
                        assert false;
                    }
                    wait(signal);
                }
            }
        } else {
            if (oldOwner != -1 && !lexprod_lt(M, oldM) && wasWaitingForGlobalLock) {
                leak has_at<owner_signal_info>(_, ownerSignalsId, oldOwner, owner_signal_info(?ownerSignal, ?betaCallsInfoId, ?globalOwnerChangedListId));
                open nb_beta_calls_seen(?nbBetaCallsSeen);
                if (nbBetaCallsSeen == 0) {
                    oldDegree = cons(3, zeros(ticketlock_M_nb_dims + 1));
                    leak wait_perm(?pp, ownerSignal, L, ticketlock_acquire);
                    is_ancestor_of_trans(pp, oldp, p1);
                } else {
                    open post_beta_call_info(?globalOwnerSeenHandleId, ?cohortLockWasHeld);
                    leak is_lower_bound(globalOwnerSeenHandleId, ownerIncrBox, ?globalOwnerSeen);
                    leak has_at<beta_call_info>(_, betaCallsInfoId, nbBetaCallsSeen - 1, beta_call_info(?betaCallGlobalOwner, ?globalM, ?signal, _));
                    assert call_below_perm_lex(?pp, _, _);
                    is_ancestor_of_trans(pp, oldp, p1);
                    if (globalOwnerSeen == betaCallGlobalOwner) {
                        open global_owner_seen_info_handle_id(?globalOwnerSeenInfoHandleId, ?passCountHandleId);
                        leak has_at<global_round_info>(globalOwnerSeenInfoHandleId, roundsInfoId, globalOwnerSeen, global_round_info(?ownerCohort, ?ownerEnqueueIncrBoxId, ?ownerQueueListId, ?ownerWaiteeListId, ?ownerIncrBoxId, ?ownerCohortHeldIncrBoxId, ?initialClientOwner, ?initialLocalOwner));
                        leak is_lower_bound(passCountHandleId, ownerIncrBoxId, ?passCount);
                        oldDegree = cons(2, append(globalM, {MAX_PASS_COUNT - passCount + 1}));
                        if (!cohortLockWasHeld) {
                            leak has_at<void *>(_, ownerWaiteeListId, _, ?waiteeSignal);
                            leak wait_perm(pp, waiteeSignal, _, _);
                        } else {
                            open cohort_held_handle_id(?cohortHeldHandleId);
                            leak is_lower_bound(cohortHeldHandleId, ownerCohortHeldIncrBoxId, _);
                        }
                    } else {
                        oldDegree = cons(2, append(globalM, {0}));
                        open wait_inv_global_owner_changed_handle(?waitInvGlobalOwnerChangedHandle);
                        leak has_at<bool>(waitInvGlobalOwnerChangedHandle, _, _, _);
                        leak wait_perm(_, signal, L, ticketlock_acquire);
                    }
                }
            }
            if (!cohort->releasing) {
                assert nth(globalOwner, roundsInfo) == global_round_info(_, _, _, _, ?incrBoxId, _, ?initialClientOwner, ?initialLocalOwner);
                if (oldOwner == -1 || lexprod_lt(M, oldM) || wasWaitingForGlobalLock) {
                    lexprod_lt_append_r(M, cons(1, zeros(ticketlock_M_nb_dims + 1)), oldDegree);
                    if (oldClientOwner != -1 && lexprod_lt(cons(1, append(M, oldDegree)), oldClientM))
                        lexprod_lt_trans(
                            cons(1, append(M, cons(1, zeros(ticketlock_M_nb_dims + 1)))),
                            cons(1, append(M, oldDegree)),
                            oldClientM);
                    call_below_perm_lex_weaken(append(M, cons(1, zeros(ticketlock_M_nb_dims + 1))));
                    leak call_below_perm(_, cohortlock_acquire);
                    create_has_at<int>(globalOwnersId, owner);
                    handle globalOwnerHandle = create_has_at<global_round_info>(roundsInfoId, globalOwner);
                    consuming_box_predicate incr_box(incrBoxId, ?passedCount)
                    perform_action noop() {}
                    producing_fresh_handle_predicate is_lower_bound(passedCount);
                    assert is_lower_bound(?passCountHandleId, incrBoxId, passedCount);
                    close wait_inv_holding_global_lock_info(globalOwnerHandle, passCountHandleId);
                } else if (!wasHoldingGlobalLock) {
                    match_has_at<void *>(releaseSignalsId);
                    assert false;
                } else {
                    assert call_below_perm_lex(?pp, _, _);
                    is_ancestor_of_trans(pp, oldp, p1);
                    match_has_at<int>(globalOwnersId);
                    assert wait_inv_holding_global_lock_info(?globalOwnerHandle, ?passCountHandle);
                    match_has_at_<global_round_info>(globalOwnerHandle);
                }
                wop(cons(1, append(M, cons(1, zeros(ticketlock_M_nb_dims + 1)))));
                call_perm__weaken(cohortlock_acquire, ticketlock_acquire);
            } else {
                if (oldOwner != -1 && !lexprod_lt(M, oldM) && wasHoldingGlobalLock) {
                    assert call_below_perm_lex(?pp, _, _);
                    is_ancestor_of_trans(pp, oldp, p1);
                    open wait_inv_holding_global_lock_info(?globalOwnerHandle, ?passCountHandle);
                    leak has_at<int>(_, globalOwnersId, _, _);
                    leak has_at<global_round_info>(globalOwnerHandle, _, _, _);
                    leak is_lower_bound(passCountHandle, _, _);
                    oldDegree = cons(1, zeros(ticketlock_M_nb_dims + 1));
                }
                assert growing_list<void *>(releaseSignalsId, ?releaseSignals);
                void *releaseSignal = nth(owner, releaseSignals);
                if (oldOwner == -1 || lexprod_lt(M, oldM) || wasWaitingForGlobalLock || wasHoldingGlobalLock) {
                    lexprod_lt_append_r(M,
                        cons(0, zeros(ticketlock_M_nb_dims + 1)),
                        oldDegree);
                    if (oldClientOwner != -1 && oldClientM != cons(1, append(M, oldDegree)) && !(oldOwner != -1 && !lexprod_lt(M, oldM) && wasHoldingGlobalLock))
                        lexprod_lt_trans(
                            cons(1, append(M, cons(0, zeros(ticketlock_M_nb_dims + 1)))),
                            cons(1, append(M, oldDegree)),
                            oldClientM);
                    call_below_perm_lex_weaken(append(M, cons(0, zeros(ticketlock_M_nb_dims + 1))));
                    create_wait_perm(releaseSignal, L, ticketlock_acquire);
                    close exists(pair(false, false));
                    create_has_at<void *>(releaseSignalsId, owner);
                } else {
                    match_has_at<void *>(releaseSignalsId);
                    assert wait_perm(?pp, _, _, _);
                    is_ancestor_of_trans(pp, oldp, p1);
                }
                wait(releaseSignal);
            }
        }

        assert wait_inv(?newClientOwner, ?newClientM, ?newClientP, ?newClientObs);
        if (!forall(map(snd, newClientObs), (func_lt_level)(ticketlock_acquire))) {
            level badLevel = not_forall(map(snd, newClientObs), (func_lt_level)(ticketlock_acquire));
            forall_elim(map(snd, newClientObs), (func_lt_level)(cohortlock_acquire), badLevel);
            assert false;
        }
            
        void *myNewSignal = create_signal();
        init_signal(myNewSignal, L);
        assert ghost_list(queueListId, ?newQueue);
        ghost_list_insert(queueListId, {}, newQueue, pair(myNewSignal, f));
        close signal_pred(cohort)(pair(myNewSignal, f));
        close foreach(cons(pair(myNewSignal, f), newQueue), signal_pred(cohort));
        
        close queue_info(cohort, enqueueIncrBoxId, queueListId, waiteeListId, owner, true, passing);
        close cohortlock_inv(lock, inv, ownerIncrBox, roundsInfoId)();
        close_atomic_space(create_cohortlock, cohortlock_inv(lock, inv, ownerIncrBox, roundsInfoId));
        close COHORT_INV();
        close_atomic_space(create_cohort, COHORT_INV);
        
        close cohort_ticketlock_inv(cohort)(owner, true);
        close wait_inv_(owner, M, p1, _);
    };
    @*/
    /*@
    produce_lemma_function_pointer_chunk ticketlock_acquire_ghost_op(cohort_ticketlock_inv(cohort), wait_inv_, post_, currentThread)() {
        assert obs_(acquireThread, ?p1, ?obs1);
        open wait_inv_(?oldOwner, ?oldM, ?p0, obs1);
        assert wait_inv(?oldClientOwner, ?oldClientM, ?oldClientP, ?oldClientObs);
        is_ancestor_of_trans(oldClientP, p0, p1);
        
        // Clean up wait_inv_ ghost state
        if (oldOwner == -1) {
            leak call_below_perm_(_, _);
        } else {
            list<int> oldDegree;
            leak call_below_perm_lex(_, _, _);
            open exists<pair<bool, bool> >(pair(?wasWaitingForGlobalLock, ?wasHoldingGlobalLock));
            if (wasWaitingForGlobalLock) {
                leak has_at(_, ownerSignalsId, oldOwner, owner_signal_info(?oldOwnerSignal, ?oldBetaCallsInfoId, ?oldGlobalOwnerChangedListId));
                open nb_beta_calls_seen(?nbBetaCallsSeen);
                if (nbBetaCallsSeen == 0) {
                    oldDegree = cons(1, append(oldM, cons(3, zeros(ticketlock_M_nb_dims + 1))));
                    leak wait_perm(_, _, _, _);
                } else {
                    open post_beta_call_info(?oldGlobalOwnerSeenHandleId, ?cohortLockWasHeld);
                    leak has_at(_, oldBetaCallsInfoId, nbBetaCallsSeen - 1, beta_call_info(?betaCallGlobalOwner, ?globalM, ?signal, _));
                    leak is_lower_bound(oldGlobalOwnerSeenHandleId, ownerIncrBox, ?globalOwnerSeen);
                    if (globalOwnerSeen == betaCallGlobalOwner) {
                        open global_owner_seen_info_handle_id(?globalOwnerInfoHandleId, ?passCountHandleId);
                        leak has_at(globalOwnerInfoHandleId, roundsInfoId, globalOwnerSeen, global_round_info(?ownerCohort, ?ownerEnqueueIncrBoxId, ?ownerQueueListId, ?ownerWaiteeListId, ?ownerIncrBoxId, ?ownerCohortHeldIncrBoxId, ?initialClientOwner, ?initialLocalOwner));
                        leak is_lower_bound(passCountHandleId, ownerIncrBoxId, ?passCount);
                        oldDegree = cons(1, append(oldM, cons(2, append(globalM, {MAX_PASS_COUNT - passCount + 1}))));
                        if (!cohortLockWasHeld) {
                            leak has_at<void *>(_, ownerWaiteeListId, _, ?waiteeSignal);
                            leak wait_perm(_, waiteeSignal, _, _);
                        } else {
                            open cohort_held_handle_id(?cohortHeldHandleId);
                            leak is_lower_bound(cohortHeldHandleId, _, _);
                        }
                    } else {
                        oldDegree = cons(1, append(oldM, cons(2, append(globalM, {0}))));
                        open wait_inv_global_owner_changed_handle(?waitInvGlobalOwnerChangedHandle);
                        leak has_at<bool>(waitInvGlobalOwnerChangedHandle, _, _, _);
                        leak wait_perm(_, _, _, _);
                    }
                }
            } else if (wasHoldingGlobalLock) {
                leak has_at<int>(_, globalOwnersId, oldOwner, ?globalOwner);
                open wait_inv_holding_global_lock_info(?globalOwnerHandle, ?passCountHandleId);
                leak has_at<global_round_info>(globalOwnerHandle, roundsInfoId, globalOwner, _);
                leak is_lower_bound(passCountHandleId, _, ?passedCount);
                oldDegree = cons(1, append(oldM, cons(1, zeros(ticketlock_M_nb_dims + 1))));
            } else {
                leak has_at<void *>(_, releaseSignalsId, oldOwner, ?releaseSignal);
                leak wait_perm(_, releaseSignal, _, _);
                oldDegree = cons(1, append(oldM, cons(0, zeros(ticketlock_M_nb_dims + 1))));
            }
            assert length(oldDegree) == 2*ticketlock_M_nb_dims + 3;
            if (oldClientOwner != -1 && lexprod_lt(oldDegree, oldClientM))
                lexprod_lt_trans(
                    cons(0, cons(1, zeros(2*ticketlock_M_nb_dims + 1))),
                    oldDegree,
                    oldClientM);
        }

        assert ghost_list_member_handle<pair<void *, real> >(queueListId, pair(?mySignal, f));
        open cohort_ticketlock_inv(cohort)(?owner, false);
        
        // First, set our queue signal.
        assert atomic_spaces(?spaces);
        if (mem(pair(create_cohort, COHORT_INV), spaces)) {
            mem_map(pair(create_cohort, COHORT_INV), spaces, fst);
            forall_elim(map(fst, spaces), (func_gt)(ticketlock_dispose), create_cohort);
            assert false;
        }
        open_atomic_space(create_cohort, COHORT_INV);
        open COHORT_INV();
        if (mem(pair(create_cohortlock, cohortlock_inv(lock, inv, ownerIncrBox, roundsInfoId)), spaces)) {
            mem_map(pair(create_cohortlock, cohortlock_inv(lock, inv, ownerIncrBox, roundsInfoId)), spaces, fst);
            forall_elim(map(fst, spaces), (func_gt)(ticketlock_dispose), create_cohortlock);
            assert false;
        }
        open_atomic_space(create_cohortlock, cohortlock_inv(lock, inv, ownerIncrBox, roundsInfoId));
        open cohortlock_inv(lock, inv, ownerIncrBox, roundsInfoId)();
        if (cohort->_passing) {
            match_has_at(roundsInfoId);
            merge_fractions cohort_owner(cohort, _);
            merge_fractions cohort_held(cohort, _);
        }
        int globalOwner = lock->owner;
        assert growing_list<global_round_info>(roundsInfoId, ?roundsInfo);
        open queue_info(cohort, enqueueIncrBoxId, queueListId, waiteeListId, owner, false, ?passing);
        
        assert ghost_list(queueListId, ?queue);
        ghost_list_remove_remove(queueListId, pair(mySignal, f));
        foreach_remove(pair(mySignal, f), queue);
        open signal_pred(cohort)(pair(mySignal, f));
        set_signal(mySignal);
        leak signal(mySignal, L, true);
        
        if (!forall(map(fst, spaces), (func_gt)(cohortlock_dispose))) {
            void *badFunc = not_forall(map(fst, spaces), (func_gt)(cohortlock_dispose));
            forall_elim(map(fst, spaces), (func_gt)(ticketlock_dispose), badFunc);
            assert false;
        }
        
        if (!forall(map(snd, oldClientObs), (level_lt)(L))) {
            level badLevel = not_forall(map(snd, oldClientObs), (level_lt)(L));
            forall_elim(map(snd, oldClientObs), (func_lt_level)(cohortlock_acquire), badLevel);
            assert false;
        }
        
        if (!forall(map(snd, oldClientObs), (func_lt_level)(ticketlock_acquire))) {
            level badLevel = not_forall(map(snd, oldClientObs), (func_lt_level)(ticketlock_acquire));
            forall_elim(map(snd, oldClientObs), (func_lt_level)(cohortlock_acquire), badLevel);
            assert false;
        }
        
        cohort->held = true;
        cohort->queueSizeExcess = 1;
        if (cohort->_passing) {
            leak is_cohortlock_wait_ghost_op(wop, inv, wait_inv, acquireThread);
            owner_signal_info ownerSignalInfo; // Leave uninitialized; any value will do.
            growing_list_add(ownerSignalsId, ownerSignalInfo);
            assert nth(globalOwner, roundsInfo) == global_round_info(cohort, enqueueIncrBoxId, queueListId, waiteeListId, ?incrBoxId, ?cohortHeldIncrBoxId, ?initialClientOwner, ?initialLocalOwner);
            consuming_box_predicate incr_box(cohortHeldIncrBoxId, ?passedCount)
            perform_action incr() {}
            producing_box_predicate incr_box(passedCount + 1);
            aop();
            leak is_cohortlock_acquire_ghost_op(aop, inv, wait_inv, post, acquireThread);
            create_has_at<global_round_info>(roundsInfoId, globalOwner);
            create_has_at<int>(globalOwnersId, owner);
        } else {
            void *ownerSignal = create_signal();
            init_signal(ownerSignal, L);
            cohort->betaCallsInfo = {};
            box betaCallsInfoId = create_growing_list<beta_call_info>();
            box globalOwnerChangedListId = create_growing_list<bool>();
            assert growing_list<owner_signal_info>(ownerSignalsId, ?ownerSignals);
            growing_list_add(ownerSignalsId, owner_signal_info(ownerSignal, betaCallsInfoId, globalOwnerChangedListId));
            create_has_at<owner_signal_info>(ownerSignalsId, owner);
            nth_append_r(ownerSignals, {owner_signal_info(ownerSignal, betaCallsInfoId, globalOwnerChangedListId)}, 0);
        }
        
        close queue_info(cohort, enqueueIncrBoxId, queueListId, waiteeListId, owner, true, cohort->_passing);
        close cohortlock_inv(lock, inv, ownerIncrBox, roundsInfoId)();
        close_atomic_space(create_cohortlock, cohortlock_inv(lock, inv, ownerIncrBox, roundsInfoId));
        close COHORT_INV();
        close_atomic_space(create_cohort, COHORT_INV);
        
        close cohort_ticketlock_inv(cohort)(owner, true);
        close post_(owner);
    };
    @*/
    //@ is_ancestor_of_refl(p);
    //@ produce_call_below_perm_();
    //@ close wait_inv_(-1, {}, p, cons(pair(initialSignal, L), obs));
    ticketlock_acquire(cohort->lock);
    //@ open post_(?ticket);
  }
  {
      /*@
      predicate pre_() =
          [f]atomic_space(create_cohort, COHORT_INV) &*&
          [1/2]cohort->queueSizeExcess |-> 1;
      predicate post_() =
          [f]atomic_space(create_cohort, COHORT_INV) &*&
          [1/2]cohort->queueSizeExcess |-> 0;
      @*/
      /*@
      produce_lemma_function_pointer_chunk atomic_decrement_counter_ghost_op(&cohort->queueSize, pre_, post_, currentThread)() {
        open pre_();
        open_atomic_space(create_cohort, COHORT_INV);
        open COHORT_INV();
        if (cohort->_passing) {
            open_atomic_space(create_cohortlock, cohortlock_inv(lock, inv, ownerIncrBox, roundsInfoId));
            open cohortlock_inv(lock, inv, ownerIncrBox, roundsInfoId)();
            match_has_at(roundsInfoId);
            merge_fractions cohort_owner(cohort, _);
            merge_fractions cohort_held(cohort, _);
        }
        open queue_info(cohort, enqueueIncrBoxId, queueListId, waiteeListId, ?owner, ?held, ?passing);
        
        assert is_atomic_decrement_counter_op(?op, &cohort->queueSize, ?P, ?Q);
        op();
        leak is_atomic_decrement_counter_op(op, &cohort->queueSize, P, Q);
        
        cohort->queueSizeExcess = 0;
        
        close queue_info(cohort, enqueueIncrBoxId, queueListId, waiteeListId, owner, held, passing);
        if (cohort->_passing) {
            close cohortlock_inv(lock, inv, ownerIncrBox, roundsInfoId)();
            close_atomic_space(create_cohortlock, cohortlock_inv(lock, inv, ownerIncrBox, roundsInfoId));
        }
        
        close COHORT_INV();
        close_atomic_space(create_cohort, COHORT_INV);
        close post_();
      };
      @*/
      //@ close pre_();
      atomic_decrement_counter(&cohort->queueSize);
      //@ open post_();
  }
  if (!cohort->passing) {
    //@ assert obs(?p1, ?obs1);
    //@ assert has_at(?ownerSignalHandle, ownerSignalsId, ?ticket, owner_signal_info(?ownerSignal, ?betaCallsInfoId, ?globalOwnerChangedListId));
    {
        /*@
        predicate cohort_held_handle_id(handle cohortHeldHandleId) = true;
        predicate wait_inv_(int oldGlobalOwner, list<int> oldGlobalM, list<pathcomp> oldp, list<pair<void *, level> > obs2) =
            is_ancestor_of(p1, oldp) == true &*&
            [f]atomic_space(create_cohort, COHORT_INV) &*&
            [1/4]cohort->_passing |-> false &*&
            [1/4]cohort->_passedCount |-> ?passedCount &*&
            [1/2]cohort->queueSizeExcess |-> 0 &*&
            [1/2]cohort->releasing |-> false &*&
            [1/8]cohort->owner |-> ticket &*&
            [1/8]cohort->held |-> true &*&
            wait_inv(?oldClientOwner, ?oldClientM, ?oldClientPhase, ?clientObs) &*& is_ancestor_of(oldClientPhase, oldp) == true &*&
            forall(map(snd, clientObs), (func_lt_level)(cohortlock_acquire)) == true &*&
            is_cohortlock_wait_ghost_op(wop, inv, wait_inv, currentThread) &*&
            is_cohortlock_acquire_ghost_op(aop, inv, wait_inv, post, currentThread) &*&
            has_at(ownerSignalHandle, ownerSignalsId, ticket, owner_signal_info(ownerSignal, betaCallsInfoId, globalOwnerChangedListId)) &*&
            [1/2]cohort->betaCallsInfo |-> ?betaCallsInfo &*&
            obs2 == cons(pair(?currentSignal, L), clientObs) &*&
            length(betaCallsInfo) == 0 ?
                oldGlobalOwner == -1 &*&
                oldClientOwner == -1 || lexprod_lt(cons(0, cons(1, zeros(2*ticketlock_M_nb_dims + 1))), oldClientM) &*&
                call_below_perm_(currentThread, cohortlock_acquire) &*&
                currentSignal == ownerSignal
            :
                oldGlobalOwner != -1 &*&
                nth(length(betaCallsInfo) - 1, betaCallsInfo) == beta_call_info(oldGlobalOwner, oldGlobalM, ?signal, ?roundsInfoHandleId) &*&
                length(oldGlobalM) == ticketlock_M_nb_dims &*&
                exists(pair(?globalOwnerInfoHandleId, pair(?passCountHandleId, ?cohortLockWasHeld))) &*&
                has_at(globalOwnerInfoHandleId, roundsInfoId, oldGlobalOwner, global_round_info(?ownerCohort, ?ownerEnqueueIncrBoxId, ?ownerQueueListId, ?ownerWaiteeListId, ?ownerIncrBoxId, ?ownerCohortHeldIncrBoxId, ?initialClientOwner, ?initialLocalOwner)) &*&
                is_lower_bound(passCountHandleId, ownerIncrBoxId, ?passCount) &*& 0 <= passCount &*& passCount <= MAX_PASS_COUNT &*&
                call_below_perm_lex(?pp, cohortlock_acquire, append(oldGlobalM, {MAX_PASS_COUNT - passCount})) &*&
                is_ancestor_of(pp, oldp) == true &*&
                currentSignal == signal &*&
                !cohortLockWasHeld ?
                    oldClientOwner == -1 || lexprod_lt(cons(0, cons(0, append(oldGlobalM, cons(MAX_PASS_COUNT - passCount, zeros(ticketlock_M_nb_dims))))), oldClientM) &*&
                    has_at(_, ownerWaiteeListId, initialLocalOwner + passCount, ?waiteeSignal) &*&
                    wait_perm(pp, waiteeSignal, L, ticketlock_acquire)
                :
                    cohort_held_handle_id(?cohortHeldHandleId) &*&
                    is_lower_bound(cohortHeldHandleId, ownerCohortHeldIncrBoxId, passCount + 1) &*&
                    oldClientOwner == initialClientOwner + passCount &*&
                    oldClientM == cons(0, cons(0, append(oldGlobalM, cons(MAX_PASS_COUNT - passCount, zeros(ticketlock_M_nb_dims)))));
        predicate post_(int globalTicket) =
            [f]atomic_space(create_cohort, COHORT_INV) &*&
            [1/4]cohort->_passing |-> true &*&
            [1/4]cohort->_passedCount |-> 0 &*&
            [1/8]cohort->held |-> true &*&
            [1/8]cohort->owner |-> ticket &*&
            [1/2]cohort->queueSizeExcess |-> 0 &*&
            [1/2]cohort->releasing |-> false &*&
            has_at(_, roundsInfoId, globalTicket, global_round_info(cohort, enqueueIncrBoxId, queueListId, waiteeListId, ?incrBoxId, ?cohortHeldIncrBoxId, ?clientOwner, ticket)) &*&
            has_at(_, globalOwnersId, ticket, globalTicket) &*&
            post(clientOwner);
        @*/
        /*@
        produce_lemma_function_pointer_chunk ticketlock_wait_ghost_op(cohortlock_ticketlock_inv(lock), wait_inv_, currentThread)(globalM) {
            open cohortlock_ticketlock_inv(lock)(?globalOwner, true);
            open wait_inv_(?oldGlobalOwner, ?oldGlobalM, ?oldp, ?oldobs);
            assert wait_inv(?oldClientOwner, ?oldClientM, ?oldClientPhase, ?clientObs);
            assert obs(?p2, cons(pair(?oldSignal, L), clientObs));
            is_ancestor_of_trans(p1, oldp, p2);
            
            if (!forall(map(snd, clientObs), (level_lt)(L))) {
                level badLevel = not_forall(map(snd, clientObs), (level_lt)(L));
                forall_elim(map(snd, clientObs), (func_lt_level)(cohortlock_acquire), badLevel);
                assert false;
            }
            
            assert atomic_spaces(?spaces);
            if (mem(pair(create_cohort, COHORT_INV), spaces)) {
                mem_map(pair(create_cohort, COHORT_INV), spaces, fst);
                forall_elim(map(fst, spaces), (func_gt)(ticketlock_dispose), create_cohort);
                assert false;
            }
            open_atomic_space(create_cohort, COHORT_INV);
            open COHORT_INV();
            if (mem(pair(create_cohortlock, cohortlock_inv(lock, inv, ownerIncrBox, roundsInfoId)), spaces)) {
                mem_map(pair(create_cohortlock, cohortlock_inv(lock, inv, ownerIncrBox, roundsInfoId)), spaces, fst);
                forall_elim(map(fst, spaces), (func_gt)(ticketlock_dispose), create_cohortlock);
                assert false;
            }
            open_atomic_space(create_cohortlock, cohortlock_inv(lock, inv, ownerIncrBox, roundsInfoId));
            open cohortlock_inv(lock, inv, ownerIncrBox, roundsInfoId)();
            
            match_has_at_<owner_signal_info>(ownerSignalHandle);
            merge_fractions growing_list<beta_call_info>(betaCallsInfoId, _);
            assert growing_list<beta_call_info>(betaCallsInfoId, ?betaCallsInfo);
            
            if (length(betaCallsInfo) != 0) {
                assert nth(length(betaCallsInfo) - 1, betaCallsInfo) == beta_call_info(oldGlobalOwner, oldGlobalM, oldSignal, ?roundsInfoHandleId);
                match_has_at_<global_round_info>(roundsInfoHandleId);
                leak has_at<global_round_info>(roundsInfoHandleId, roundsInfoId, oldGlobalOwner, _);
                assert growing_list<bool>(globalOwnerChangedListId, ?globalOwnerChangedList);
                if (length(globalOwnerChangedList) != length(betaCallsInfo) - 1) {
                    open global_owner_changed_handle(?globalOwnerChangedHandle);
                    consuming_box_predicate incr_box(ownerIncrBox, globalOwner)
                    consuming_handle_predicate is_lower_bound(globalOwnerChangedHandle, oldGlobalOwner + 1)
                    perform_action noop() {};
                }
            }
            
            handle globalOwnerInfoHandleId = create_has_at<global_round_info>(roundsInfoId, globalOwner);
            assert has_at<global_round_info>(globalOwnerInfoHandleId, roundsInfoId, globalOwner, global_round_info(?ownerCohort, ?ownerEnqueueIncrBoxId, ?ownerQueueListId, ?ownerWaiteeListId, ?ownerIncrBoxId, ?ownerCohortHeldIncrBoxId, ?initialClientOwner, ?initialLocalOwner));
            match_has_at_<global_round_info>(globalOwnerInfoHandleId);
            consuming_box_predicate incr_box(ownerIncrBoxId, ?ownerPassCount)
            perform_action noop() {}
            producing_fresh_handle_predicate is_lower_bound(ownerPassCount);
            assert is_lower_bound(?passCountHandleId, ownerIncrBoxId, ownerPassCount);
            
            bool samePassCount = false;
            if (oldGlobalOwner == -1) {
                if (oldClientOwner != -1)
                    lexprod_lt_trans(
                        cons(0, cons(0, append(globalM, cons(MAX_PASS_COUNT - ownerPassCount, zeros(ticketlock_M_nb_dims))))),
                        cons(0, cons(1, zeros(2*ticketlock_M_nb_dims + 1))),
                        oldClientM);
                pathize_call_below_perm__lex(append(globalM, {MAX_PASS_COUNT - ownerPassCount}));
                is_ancestor_of_refl(p2);
            } else {
                assert call_below_perm_lex(?pp, _, _);
                is_ancestor_of_trans(pp, oldp, p2);
                if (lexprod_lt(globalM, oldGlobalM)) {
                    open exists(pair(?oldGlobalOwnerInfoHandleId, pair(?oldPassCountHandleId, ?oldCohortLockWasHeld)));
                    match_has_at_(oldGlobalOwnerInfoHandleId);
                    leak has_at(oldGlobalOwnerInfoHandleId, roundsInfoId, oldGlobalOwner, global_round_info(?oldOwnerCohort, ?oldOwnerEnqueueIncrBoxId, ?oldOwnerQueueListId, ?oldOwnerWaiteeListId, ?oldOwnerIncrBoxId, ?oldOwnerCohortHeldIncrBoxId, ?oldInitialClientOwner, ?oldInitialLocalOwner));
                    leak is_lower_bound(oldPassCountHandleId, oldOwnerIncrBoxId, ?oldPassCount);
                    lexprod_lt_append_l(
                        globalM, {MAX_PASS_COUNT - ownerPassCount},
                        oldGlobalM, {MAX_PASS_COUNT - oldPassCount});
                    call_below_perm_lex_weaken(append(globalM, {MAX_PASS_COUNT - ownerPassCount}));
                    lexprod_lt_append_l(
                        globalM, cons(MAX_PASS_COUNT - ownerPassCount, zeros(ticketlock_M_nb_dims)),
                        oldGlobalM, cons(MAX_PASS_COUNT - oldPassCount, zeros(ticketlock_M_nb_dims)));
                    if (!oldCohortLockWasHeld) {
                        if (oldClientOwner != -1) {
                            lexprod_lt_trans(
                                cons(0, cons(0, append(globalM, cons(MAX_PASS_COUNT - ownerPassCount, zeros(ticketlock_M_nb_dims))))),
                                cons(0, cons(0, append(oldGlobalM, cons(MAX_PASS_COUNT - oldPassCount, zeros(ticketlock_M_nb_dims))))),
                                oldClientM);
                        }
                        leak has_at<void *>(_, oldOwnerWaiteeListId, _, _);
                        leak wait_perm(_, _, _, _);
                    } else {
                        open cohort_held_handle_id(?oldCohortHeldHandleId);
                        leak is_lower_bound(oldCohortHeldHandleId, _, _);
                    }
                } else {
                    open exists(pair(?oldGlobalOwnerInfoHandleId, pair(?oldPassCountHandleId, ?oldCohortLockWasHeld)));
                    match_has_at_(oldGlobalOwnerInfoHandleId);
                    leak has_at(oldGlobalOwnerInfoHandleId, roundsInfoId, oldGlobalOwner, global_round_info(?oldOwnerCohort, ?oldOwnerEnqueueIncrBoxId, ?oldOwnerQueueListId, ?oldOwnerWaiteeListId, ?oldOwnerIncrBoxId, ?oldOwnerCohortHeldIncrBoxId, ?oldInitialClientOwner, ?oldInitialLocalOwner));
                    consuming_box_predicate incr_box(ownerIncrBoxId, ownerPassCount)
                    consuming_handle_predicate is_lower_bound(oldPassCountHandleId, ?oldPassCount)
                    perform_action noop() {};
                    if (oldPassCount < ownerPassCount) {
                        lexprod_lt_append_r(globalM, {MAX_PASS_COUNT - ownerPassCount}, {MAX_PASS_COUNT - oldPassCount});
                        call_below_perm_lex_weaken(append(globalM, {MAX_PASS_COUNT - ownerPassCount}));
                        lexprod_lt_append_r(globalM,
                            cons(MAX_PASS_COUNT - ownerPassCount, zeros(ticketlock_M_nb_dims)),
                            cons(MAX_PASS_COUNT - oldPassCount, zeros(ticketlock_M_nb_dims)));
                        if (!oldCohortLockWasHeld) {
                            if (oldClientOwner != -1)
                                lexprod_lt_trans(
                                    cons(0, cons(0, append(globalM, cons(MAX_PASS_COUNT - ownerPassCount, zeros(ticketlock_M_nb_dims))))),
                                    cons(0, cons(0, append(globalM, cons(MAX_PASS_COUNT - oldPassCount, zeros(ticketlock_M_nb_dims))))),
                                    oldClientM);
                            leak has_at<void *>(_, oldOwnerWaiteeListId, _, _);
                            leak wait_perm(_, _, _, _);
                        } else {
                            open cohort_held_handle_id(?oldCohortHeldHandleId);
                            leak is_lower_bound(oldCohortHeldHandleId, _, _);
                        }
                    } else {
                        samePassCount = true;
                        if (!oldCohortLockWasHeld && ownerCohort->held) {
                            leak has_at<void *>(_, ownerWaiteeListId, _, _);
                            leak wait_perm(_, _, _, _);
                            consuming_box_predicate incr_box(ownerCohortHeldIncrBoxId, _)
                            perform_action noop() {}
                            producing_fresh_handle_predicate is_lower_bound(ownerPassCount + 1);
                            assert is_lower_bound(?cohortHeldHandleId, ownerCohortHeldIncrBoxId, ownerPassCount + 1);
                            close cohort_held_handle_id(cohortHeldHandleId);
                        } else if (oldCohortLockWasHeld) {
                            assert cohort_held_handle_id(?cohortHeldHandleId);
                            consuming_box_predicate incr_box(ownerCohortHeldIncrBoxId, _)
                            consuming_handle_predicate is_lower_bound(cohortHeldHandleId, ownerPassCount + 1)
                            perform_action noop() {}
                            producing_handle_predicate is_lower_bound(cohortHeldHandleId, ownerPassCount + 1);
                        }
                    }
                }
            }
            
            is_ancestor_of_trans(oldClientPhase, oldp, p2);
            
            set_signal(oldSignal);
            leak signal(oldSignal, L, true);
            
            handle roundsInfoHandleId = create_has_at<global_round_info>(roundsInfoId, globalOwner);
            
            if (!forall(map(fst, spaces), (func_gt)(cohortlock_dispose))) {
                void *badName = not_forall(map(fst, spaces), (func_gt)(cohortlock_dispose));
                forall_elim(map(fst, spaces), (func_gt)(ticketlock_dispose), badName);
                assert false;
            }
            
            if (!ownerCohort->held) {
                open queue_info(ownerCohort, ownerEnqueueIncrBoxId, ownerQueueListId, ownerWaiteeListId, ?cohortOwner, false, true);
                if (!samePassCount) {
                    assert [_]growing_list<void *>(ownerWaiteeListId, ?waiteeSignals);
                    create_has_at(ownerWaiteeListId, initialLocalOwner + ownerPassCount);
                    create_wait_perm(nth(initialLocalOwner + ownerPassCount, waiteeSignals), L, ticketlock_acquire);
                }
                assert has_at<void *>(?waiteeSignalHandle, ownerWaiteeListId, initialLocalOwner + ownerPassCount, ?waiteeSignal);
                match_has_at_<void *>(waiteeSignalHandle);
                assert ghost_list<pair<void *, real> >(ownerQueueListId, ?ownerQueue);
                pair<void *, real> queueElem = mem_map_mem(waiteeSignal, ownerQueue, fst);
                foreach_remove(queueElem, ownerQueue);
                open signal_pred(ownerCohort)(queueElem);
                wait(waiteeSignal);
                close signal_pred(ownerCohort)(queueElem);
                foreach_unremove(queueElem, ownerQueue);
                close queue_info(ownerCohort, ownerEnqueueIncrBoxId, ownerQueueListId, ownerWaiteeListId, cohortOwner, false, true);
            } else {
                if (!samePassCount) {
                    leak call_below_perm(_, _);
                    consuming_box_predicate incr_box(ownerCohortHeldIncrBoxId, ownerPassCount + 1)
                    perform_action noop() {}
                    producing_fresh_handle_predicate is_lower_bound(ownerPassCount + 1);
                    assert is_lower_bound(?cohortHeldHandleId, ownerCohortHeldIncrBoxId, ownerPassCount + 1);
                    close cohort_held_handle_id(cohortHeldHandleId);
                }
                wop(cons(0, cons(0, append(globalM, cons(MAX_PASS_COUNT - ownerPassCount, zeros(ticketlock_M_nb_dims))))));
                is_ancestor_of_refl(p2);
                call_perm__weaken(cohortlock_acquire, ticketlock_acquire);
            }
            
            assert obs(p2, ?newClientObs);
            assert wait_inv(_, _, _, newClientObs);
            
            void *myNewSignal = create_signal();
            init_signal(myNewSignal, L);
            
            beta_call_info newBetaCallInfo = beta_call_info(globalOwner, globalM, myNewSignal, roundsInfoHandleId);
            cohort->betaCallsInfo = append(betaCallsInfo, {newBetaCallInfo});
            growing_list_add(betaCallsInfoId, newBetaCallInfo);
            nth_append_r(betaCallsInfo, {newBetaCallInfo}, 0);
            assert growing_list(betaCallsInfoId, ?newBetaCallsInfo);
            close exists(pair(globalOwnerInfoHandleId, pair(passCountHandleId, ownerCohort->held)));
            
            if (!forall_int((beta_calls_info_decreases)(newBetaCallsInfo))) {
                int i = not_forall_int((beta_calls_info_decreases)(newBetaCallsInfo));
                if (i < length(betaCallsInfo)) {
                    nth_append(betaCallsInfo, {beta_call_info(globalOwner, globalM, myNewSignal, roundsInfoHandleId)}, i);
                    nth_append(betaCallsInfo, {beta_call_info(globalOwner, globalM, myNewSignal, roundsInfoHandleId)}, i - 1);
                    forall_int_elim((beta_calls_info_decreases)(betaCallsInfo), i);
                    assert false;
                } else {
                    nth_append_r(betaCallsInfo, {beta_call_info(globalOwner, globalM, myNewSignal, roundsInfoHandleId)}, 0);
                    nth_append(betaCallsInfo, {beta_call_info(globalOwner, globalM, myNewSignal, roundsInfoHandleId)}, length(betaCallsInfo) - 1);
                    assert false;
                }
            }
            
            assert growing_list<bool>(globalOwnerChangedListId, ?globalOwnerChangedList);
            bool globalOwnerChanged = globalOwner != nth(length(betaCallsInfo) - 1, betaCallsInfo)->globalOwner;
            if (length(globalOwnerChangedList) < length(betaCallsInfo)) {
                growing_list_add(globalOwnerChangedListId, globalOwnerChanged);
                nth_append_r(globalOwnerChangedList, {globalOwnerChanged}, 0);
            }
            
            assert growing_list<bool>(globalOwnerChangedListId, ?newGlobalOwnerChangedList);
            
            if (!forall_int((global_owner_changed_ok)(newBetaCallsInfo, newGlobalOwnerChangedList))) {
                int i = not_forall_int((global_owner_changed_ok)(newBetaCallsInfo, newGlobalOwnerChangedList));
                if (i == length(betaCallsInfo)) {
                    nth_append_r(betaCallsInfo, {beta_call_info(globalOwner, globalM, myNewSignal, roundsInfoHandleId)}, 0);
                    nth_append(betaCallsInfo, {beta_call_info(globalOwner, globalM, myNewSignal, roundsInfoHandleId)}, length(betaCallsInfo) - 1);
                    assert false;
                } else {
                    nth_append(betaCallsInfo, {beta_call_info(globalOwner, globalM, myNewSignal, roundsInfoHandleId)}, i);
                    nth_append(betaCallsInfo, {beta_call_info(globalOwner, globalM, myNewSignal, roundsInfoHandleId)}, i - 1);
                    nth_append(globalOwnerChangedList, {globalOwnerChanged}, i - 1);
                    forall_int_elim((global_owner_changed_ok)(betaCallsInfo, globalOwnerChangedList), i);
                    assert false;
                }
            }
            
            close cohortlock_inv(lock, inv, ownerIncrBox, roundsInfoId)();
            close_atomic_space(create_cohortlock, cohortlock_inv(lock, inv, ownerIncrBox, roundsInfoId));
            
            close COHORT_INV();
            close_atomic_space(create_cohort, COHORT_INV);

            close wait_inv_(globalOwner, globalM, p2, cons(pair(myNewSignal, L), newClientObs));
            close cohortlock_ticketlock_inv(lock)(globalOwner, true);
            
            if (!forall(map(snd, newClientObs), (func_lt_level)(ticketlock_acquire))) {
                level badLevel = not_forall(map(snd, newClientObs), (func_lt_level)(ticketlock_acquire));
                forall_elim(map(snd, newClientObs), (func_lt_level)(cohortlock_acquire), badLevel);
                assert false;
            }
        };
        @*/
        /*@
        produce_lemma_function_pointer_chunk ticketlock_acquire_ghost_op(cohortlock_ticketlock_inv(lock), wait_inv_, post_, currentThread)() {
            open cohortlock_ticketlock_inv(lock)(?globalOwner, false);
            open wait_inv_(?oldGlobalOwner, ?oldGlobalM, ?oldp, ?oldobs);
            assert wait_inv(?oldClientOwner, ?oldClientM, ?oldClientPhase, ?clientObs);
            assert obs_(acquireThread, ?p2, cons(pair(?oldSignal, L), clientObs));
            is_ancestor_of_trans(p1, oldp, p2);
            
            assert atomic_spaces(?spaces);
            if (mem(pair(create_cohort, COHORT_INV), spaces)) {
                mem_map(pair(create_cohort, COHORT_INV), spaces, fst);
                forall_elim(map(fst, spaces), (func_gt)(ticketlock_dispose), create_cohort);
                assert false;
            }
            open_atomic_space(create_cohort, COHORT_INV);
            open COHORT_INV();
            if (mem(pair(create_cohortlock, cohortlock_inv(lock, inv, ownerIncrBox, roundsInfoId)), spaces)) {
                mem_map(pair(create_cohortlock, cohortlock_inv(lock, inv, ownerIncrBox, roundsInfoId)), spaces, fst);
                forall_elim(map(fst, spaces), (func_gt)(ticketlock_dispose), create_cohortlock);
                assert false;
            }
            open_atomic_space(create_cohortlock, cohortlock_inv(lock, inv, ownerIncrBox, roundsInfoId));
            open cohortlock_inv(lock, inv, ownerIncrBox, roundsInfoId)();
            
            match_has_at_<owner_signal_info>(ownerSignalHandle);
            merge_fractions growing_list<beta_call_info>(betaCallsInfoId, _);
            leak has_at(ownerSignalHandle, ownerSignalsId, ticket, owner_signal_info(ownerSignal, betaCallsInfoId, globalOwnerChangedListId));
            leak growing_list<beta_call_info>(betaCallsInfoId, ?betaCallsInfo);
            leak is_cohortlock_wait_ghost_op(wop, inv, wait_inv, acquireThread);
            
            if (length(betaCallsInfo) == 0) {
                leak call_below_perm_(_, _);
            } else {
                assert nth(length(betaCallsInfo) - 1, betaCallsInfo) == beta_call_info(oldGlobalOwner, oldGlobalM, oldSignal, ?roundsInfoHandleId);
                match_has_at_<global_round_info>(roundsInfoHandleId);
                leak has_at<global_round_info>(roundsInfoHandleId, roundsInfoId, oldGlobalOwner, _);
                assert growing_list<bool>(globalOwnerChangedListId, ?globalOwnerChangedList);
                if (length(globalOwnerChangedList) != length(betaCallsInfo) - 1) {
                    open global_owner_changed_handle(?globalOwnerChangedHandle);
                    consuming_box_predicate incr_box(ownerIncrBox, globalOwner)
                    consuming_handle_predicate is_lower_bound(globalOwnerChangedHandle, oldGlobalOwner + 1)
                    perform_action noop() {};
                }
            }
            
            leak growing_list<bool>(globalOwnerChangedListId, _);
            
            if (oldGlobalOwner == -1) {
            } else {
                leak call_below_perm_lex(_, _, _);
                open exists(pair(?oldGlobalOwnerInfoHandleId, pair(?oldPassCountHandleId, ?oldCohortLockWasHeld)));
                match_has_at_(oldGlobalOwnerInfoHandleId);
                leak has_at(oldGlobalOwnerInfoHandleId, roundsInfoId, oldGlobalOwner, global_round_info(?oldOwnerCohort, ?oldOwnerEnqueueIncrBoxId, ?oldOwnerQueueListId, ?oldOwnerWaiteeListId, ?oldOwnerIncrBoxId, ?oldOwnerCohortHeldIncrBoxId, ?oldInitialClientOwner, ?oldInitialLocalOwner));
                leak is_lower_bound(oldPassCountHandleId, oldOwnerIncrBoxId, ?oldPassCount);
                if (!oldCohortLockWasHeld) {
                    leak has_at<void *>(_, oldOwnerWaiteeListId, _, _);
                    leak wait_perm(_, _, _, _);
                } else {
                    open cohort_held_handle_id(?oldCohortHeldHandleId);
                    leak is_lower_bound(oldCohortHeldHandleId, _, _);
                }
            }
            
            is_ancestor_of_trans(oldClientPhase, oldp, p2);
            
            set_signal(oldSignal);
            leak signal(oldSignal, L, true);
            
            lock->held_ = true;
            cohort->_passing = true;
            cohort->_passedCount = 0;
            
            if (!forall(map(fst, spaces), (func_gt)(cohortlock_dispose))) {
                void *badName = not_forall(map(fst, spaces), (func_gt)(cohortlock_dispose));
                forall_elim(map(fst, spaces), (func_gt)(ticketlock_dispose), badName);
                assert false;
            }
            
            aop();
            leak is_cohortlock_acquire_ghost_op(aop, inv, wait_inv, post, acquireThread);
            
            assert inv(?clientOwner, true);
            
            create_box incrBoxId = incr_box(0);
            create_box cohortHeldIncrBoxId = incr_box(1);
            
            assert growing_list<global_round_info>(roundsInfoId, ?roundsInfo);
            assert length(roundsInfo) == globalOwner;
            global_round_info newRoundInfo = global_round_info(cohort, enqueueIncrBoxId, queueListId, waiteeListId, incrBoxId, cohortHeldIncrBoxId, clientOwner, ticket);
            growing_list_add(roundsInfoId, newRoundInfo);
            nth_append_r(roundsInfo, {newRoundInfo}, 0);
            
            open queue_info(cohort, enqueueIncrBoxId, queueListId, waiteeListId, ticket, true, false);
            close queue_info(cohort, enqueueIncrBoxId, queueListId, waiteeListId, ticket, true, true);
            
            assert growing_list<int>(globalOwnersId, ?globalOwners);
            growing_list_add(globalOwnersId, globalOwner);
            nth_append_r(globalOwners, {globalOwner}, 0);
            create_has_at<int>(globalOwnersId, ticket);
            handle passingGlobalOwnerHandle = create_has_at<global_round_info>(roundsInfoId, globalOwner);
            close passing_global_owner_handle(passingGlobalOwnerHandle);
            
            create_has_at(roundsInfoId, globalOwner);
            
            close cohortlock_inv(lock, inv, ownerIncrBox, roundsInfoId)();
            close_atomic_space(create_cohortlock, cohortlock_inv(lock, inv, ownerIncrBox, roundsInfoId));
            
            close COHORT_INV();
            close_atomic_space(create_cohort, COHORT_INV);
            
            close post_(globalOwner);
            close cohortlock_ticketlock_inv(lock)(globalOwner, true);
        };
        @*/
        //@ is_ancestor_of_refl(p1);
        //@ produce_call_below_perm_();
        //@ close wait_inv_(-1, {}, p1, obs1);
        //@ assert obs1 == cons(pair(ownerSignal, L), ?clientObs);
        /*@
        if (!forall(map(snd, clientObs), (func_lt_level)(ticketlock_acquire))) {
            level badLevel = not_forall(map(snd, clientObs), (func_lt_level)(ticketlock_acquire));
            forall_elim(map(snd, clientObs), (func_lt_level)(cohortlock_acquire), badLevel);
            assert false;
        }
        @*/
        ticketlock_acquire(cohort->cohortlock->lock);
        //@ open post_(?globalTicket);
    }
  }
  //@ close cohortlock_held(cohort, lock, inv, frac, f, _);
}

void cohortlock_release(cohort cohort)
/*@
requires
    obs(?p, ?obs) &*& forall(map(snd, obs), (func_lt_level)(cohortlock_acquire)) == true &*&
    cohortlock_held(cohort, ?lock, ?inv, ?frac, ?f, ?ticket) &*& is_cohortlock_release_ghost_op(?ghop, inv, ticket, p, obs, ?pre, ?post, currentThread) &*& pre();
@*/
//@ ensures obs(?p2, ?obs1) &*& post(?p1, obs1) &*& is_ancestor_of(p1, p2) == true &*& [f]cohort(cohort, lock, inv, frac);
//@ terminates;
{
  //@ open cohortlock_held(cohort, lock, inv, frac, f, ticket);
  //@ ticketlock globalLock = lock->lock;
  //@ box ownerIncrBox = lock->ownerIncrBox;
  //@ box roundsInfoId = lock->roundsInfoId;
  //@ box enqueueIncrBoxId = cohort->enqueueIncrBoxId;
  //@ int queueListId = cohort->queueListId;
  //@ box waiteeListId = cohort->waiteeListId;
  //@ box ownerSignalsId = cohort->ownerSignalsId;
  //@ box globalOwnersId = cohort->globalOwnersId;
  //@ box releaseSignalsId = cohort->releaseSignalsId;
  //@ int localTicket = cohort->owner;
  //@ assert has_at<int>(?globalOwnerHandle, globalOwnersId, localTicket, ?globalTicket);
  //@ assert has_at<global_round_info>(?globalTicketHandle, roundsInfoId, globalTicket, global_round_info(_, _, _, _, ?incrBoxId, ?cohortHeldIncrBoxId, ?initialClientOwner, ?initialLocalOwner));
  //@ int oldPassedCount = cohort->_passedCount;
  if (cohort->passedCount < MAX_PASS_COUNT) {
    unsigned long long queueSize;
    {
      /*@
      predicate pre_() =
          [1/2]cohort->queueSizeExcess |-> 0 &*&
          [1/4]cohort->_passing |-> true &*&
          [1/8]cohort->held |-> true &*&
          [1/8]cohort->owner |-> localTicket &*&
          has_at(globalOwnerHandle, globalOwnersId, localTicket, globalTicket) &*&
          [f]atomic_space(create_cohort, COHORT_INV);
      predicate post_(int result) =
          [1/2]cohort->queueSizeExcess |-> 0 &*&
          [1/4]cohort->_passing |-> true &*&
          [1/8]cohort->held |-> true &*&
          [1/8]cohort->owner |-> localTicket &*&
          has_at(globalOwnerHandle, globalOwnersId, localTicket, globalTicket) &*&
          [f]atomic_space(create_cohort, COHORT_INV) &*&
          result == 0 ? true : is_lower_bound(_, enqueueIncrBoxId, ?nbEnqueues) &*& result == nbEnqueues - localTicket - 1;
      @*/
      /*@
      produce_lemma_function_pointer_chunk atomic_load_counter_ghost_op(&cohort->queueSize, pre_, post_, currentThread)() {
          open pre_();
          open_atomic_space(create_cohort, COHORT_INV);
          open COHORT_INV();
          match_has_at_<int>(globalOwnerHandle);
          assert [_]lock->owner |-> globalTicket;
          
          assert passing_global_owner_handle(?passingGlobalOwnerHandle);
          
          open_atomic_space(create_cohortlock, cohortlock_inv(lock, inv, ownerIncrBox, roundsInfoId));
          open cohortlock_inv(lock, inv, ownerIncrBox, roundsInfoId)();
          match_has_at_<global_round_info>(passingGlobalOwnerHandle);
          merge_fractions cohort->owner |-> _;
          merge_fractions cohort->held |-> _;
          
          open queue_info(cohort, enqueueIncrBoxId, queueListId, waiteeListId, localTicket, true, true);
          merge_fractions cohort->queueSizeExcess |-> _;
          
          assert counter(&cohort->queueSize, ?result);
          assert is_atomic_load_counter_op(?op, &cohort->queueSize, ?P, ?Q);
          op();

          if (result != 0) {
                consuming_box_predicate incr_box(enqueueIncrBoxId, ?nbEnqueues)
                perform_action noop() {}
                producing_box_predicate incr_box(nbEnqueues)
                producing_fresh_handle_predicate is_lower_bound(nbEnqueues);
              }
          
          close queue_info(cohort, enqueueIncrBoxId, queueListId, waiteeListId, localTicket, true, true);
          
          close cohortlock_inv(lock, inv, ownerIncrBox, roundsInfoId)();
          close_atomic_space(create_cohortlock, cohortlock_inv(lock, inv, ownerIncrBox, roundsInfoId));
          
          close COHORT_INV();
          close_atomic_space(create_cohort, COHORT_INV);
          close post_(result);
      };
      @*/
      //@ close pre_();
      queueSize = atomic_load_counter(&cohort->queueSize);
      //@ open post_(queueSize);
    }
    cohort->passing = queueSize > 0;
  } else
    cohort->passing = false;
  //@ list<pathcomp> p01 = p;
  //@ list<pathcomp> p02 = p;
  //@ is_ancestor_of_refl(p);
  //@ list<pair<void *, level> > obs01 = obs;
  //@ list<pair<void *, level> > clientObs01 = obs;
  if (cohort->passing)
    cohort->passedCount++;
  else {
    cohort->passedCount = 0;
    {
      /*@
      predicate pre_() =
        has_at<global_round_info>(globalTicketHandle, roundsInfoId, globalTicket, global_round_info(cohort, enqueueIncrBoxId, queueListId, waiteeListId, incrBoxId, cohortHeldIncrBoxId, initialClientOwner, initialLocalOwner)) &*&
            has_at(globalOwnerHandle, globalOwnersId, localTicket, globalTicket) &*&
            [1/4]cohort->_passing |-> true &*&
            [1/4]cohort->_passedCount |-> oldPassedCount &*&
            [1/8]cohort->held |-> true &*&
            [1/8]cohort->owner |-> localTicket &*&
            //[1/2]cohort->queueSizeExcess |-> 0 &*&
            [1/2]cohort->releasing |-> false &*&
            [f]atomic_space(create_cohort, COHORT_INV) &*&
            is_cohortlock_release_ghost_op(ghop, inv, ticket, p, obs, pre, post, currentThread) &*& pre();
      predicate post_(list<pathcomp> p1, list<pair<void *, level> > obs1) =
        is_ancestor_of(p, p1) == true &*&
        has_at<global_round_info>(globalTicketHandle, roundsInfoId, globalTicket, global_round_info(cohort, enqueueIncrBoxId, queueListId, waiteeListId, incrBoxId, cohortHeldIncrBoxId, initialClientOwner, initialLocalOwner)) &*&
            has_at(globalOwnerHandle, globalOwnersId, localTicket, globalTicket) &*&
        [f]atomic_space(create_cohort, COHORT_INV) &*&
        [1/4]cohort->_passedCount |-> 0 &*&
        [1/4]cohort->_passing |-> false &*&
        [1/8]cohort->held |-> true &*&
        [1/8]cohort->owner |-> localTicket &*&
        [1/2]cohort->releasing |-> true &*&
        obs1 == cons(pair(?releaseSignal, L), ?clientObs1) &*& forall(map(snd, clientObs1), (func_lt_level)(cohortlock_acquire)) == true &*&
        has_at(_, releaseSignalsId, localTicket, releaseSignal) &*&
        post(p1, clientObs1);
      @*/
      //@ produce_func_lt(ticketlock_acquire);
      //@ produce_func_lt(ticketlock_dispose);
      //@ int releaseThread = currentThread;
      /*@
      produce_lemma_function_pointer_chunk ticketlock_release_ghost_op(cohortlock_ticketlock_inv(lock), globalTicket, p, obs, pre_, post_, currentThread)() {
        assert obs_(releaseThread, ?p1, obs);
        open pre_();
        open cohortlock_ticketlock_inv(lock)(globalTicket, true);
        
            assert atomic_spaces(?spaces);
            if (mem(pair(create_cohort, COHORT_INV), spaces)) {
                mem_map(pair(create_cohort, COHORT_INV), spaces, fst);
                forall_elim(map(fst, spaces), (func_gt)(ticketlock_dispose), create_cohort);
                assert false;
            }
            open_atomic_space(create_cohort, COHORT_INV);
            open COHORT_INV();
            if (mem(pair(create_cohortlock, cohortlock_inv(lock, inv, ownerIncrBox, roundsInfoId)), spaces)) {
                mem_map(pair(create_cohortlock, cohortlock_inv(lock, inv, ownerIncrBox, roundsInfoId)), spaces, fst);
                forall_elim(map(fst, spaces), (func_gt)(ticketlock_dispose), create_cohortlock);
                assert false;
            }
            match_has_at<int>(globalOwnersId);
            open_atomic_space(create_cohortlock, cohortlock_inv(lock, inv, ownerIncrBox, roundsInfoId));
            open cohortlock_inv(lock, inv, ownerIncrBox, roundsInfoId)();
            match_has_at_<global_round_info>(globalTicketHandle);
        match_has_at(roundsInfoId);
        open passing_global_owner_handle(?passingGlobalOwnerHandle);
        leak has_at<global_round_info>(passingGlobalOwnerHandle, roundsInfoId, globalTicket, _);
        leak incr_box(cohortHeldIncrBoxId, _);
        leak incr_box(incrBoxId, _);
        
        merge_fractions cohort_owner(cohort, _);
        merge_fractions cohort_held(cohort, _);
        merge_fractions cohort->_passing |-> _;
        merge_fractions cohort->_passedCount |-> _;
        
        if (!forall(map(fst, spaces), (func_gt)(cohortlock_dispose))) {
          void *badName = not_forall(map(fst, spaces), (func_gt)(cohortlock_dispose));
          forall_elim(map(fst, spaces), (func_gt)(ticketlock_dispose), badName);
          assert false;
        }
        ghop();
        leak is_cohortlock_release_ghost_op(ghop, _, _, _, _, _, _, _);
        assert obs_(releaseThread, p1, ?obs1);
        if (!forall(map(snd, obs1), (func_lt_level)(ticketlock_acquire))) {
          level badLevel = not_forall(map(snd, obs1), (func_lt_level)(ticketlock_acquire));
          forall_elim(map(snd, obs1), (func_lt_level)(cohortlock_acquire), badLevel);
          assert false;
        }

        cohort->_passing = false;
        cohort->_passedCount = 0;
        lock->owner++;
        lock->held_ = false;
        cohort->releasing = true;
        void *releaseSignal = create_signal();
        init_signal(releaseSignal, L);
        assert growing_list<void *>(releaseSignalsId, ?releaseSignals);
        growing_list_add(releaseSignalsId, releaseSignal);
        nth_append_r(releaseSignals, {releaseSignal}, 0);
        create_has_at(releaseSignalsId, localTicket);
        
        consuming_box_predicate incr_box(ownerIncrBox, globalTicket)
        perform_action incr() {}
        producing_box_predicate incr_box(globalTicket + 1);
        
        open queue_info(cohort, enqueueIncrBoxId, queueListId, waiteeListId, localTicket, true, true);
        close queue_info(cohort, enqueueIncrBoxId, queueListId, waiteeListId, localTicket, true, false);
        
        close COHORT_INV();
        close_atomic_space(create_cohort, COHORT_INV);
        close cohortlock_inv(lock, inv, ownerIncrBox, roundsInfoId)();
        close_atomic_space(create_cohortlock, cohortlock_inv(lock, inv, ownerIncrBox, roundsInfoId));
        
        close cohortlock_ticketlock_inv(lock)(globalTicket + 1, false);
        close post_(p1, cons(pair(releaseSignal, L), obs1));
      };
      @*/
          /*@
          if (!forall(map(snd, obs), (func_lt_level)(ticketlock_acquire))) {
              level badLevel = not_forall(map(snd, obs), (func_lt_level)(ticketlock_acquire));
              forall_elim(map(snd, obs), (func_lt_level)(cohortlock_acquire), badLevel);
              assert false;
          }
          @*/
      //@ close pre_();
      ticketlock_release(cohort->cohortlock->lock);
      //@ open post_(?p01_, ?obs01_);
      //@ p01 = p01_;
      //@ assert obs(?p2, _);
      //@ is_ancestor_of_trans(p, p01_, p2);
      //@ p02 = p2;
      //@ obs01 = obs01_;
      //@ clientObs01 = tail(obs01_);
    }
  }
  //@ bool passing = cohort->passing;
  //@ int passedCount = cohort->passedCount;
  {
    /*@
    predicate pre_() =
      has_at<global_round_info>(globalTicketHandle, roundsInfoId, globalTicket, global_round_info(cohort, enqueueIncrBoxId, queueListId, waiteeListId, incrBoxId, cohortHeldIncrBoxId, initialClientOwner, initialLocalOwner)) &*&
      has_at(globalOwnerHandle, globalOwnersId, localTicket, globalTicket) &*&
      cohort->passing |-> passing &*&
      cohort->passedCount |-> passedCount &*&
      [1/4]cohort->_passing |-> passing &*&
      [1/8]cohort->held |-> true &*&
      [1/8]cohort->owner |-> localTicket &*&
      [1/2]cohort->queueSizeExcess |-> 0 &*&
      [1/2]cohort->releasing |-> !passing &*&
      [f]atomic_space(create_cohort, COHORT_INV) &*&
      passing ?
        [1/4]cohort->_passedCount |-> oldPassedCount &*&
        ticketlock_held(globalLock, cohortlock_ticketlock_inv(lock), frac, globalTicket) &*&
        is_cohortlock_release_ghost_op(ghop, inv, ticket, p, obs, pre, post, currentThread) &*& pre() &*&
        is_lower_bound(_, enqueueIncrBoxId, ?nbEnqueues) &*& nbEnqueues > localTicket + 1
      :
        [1/4]cohort->_passedCount |-> 0 &*&
        has_at(_, releaseSignalsId, localTicket, ?releaseSignal) &*&
        obs01 == cons(pair(releaseSignal, L), _) &*&
        [frac]ticketlock(globalLock, cohortlock_ticketlock_inv(lock));
    predicate post_(list<pathcomp> p1, list<pair<void *, level> > obs1) =
      is_ancestor_of(p02, p1) == true &*&
      [f]atomic_space(create_cohort, COHORT_INV) &*&
      passing ?
        post(p1, obs1)
      :
        obs01 == cons(_, obs1);
    @*/
    //@ produce_func_lt(ticketlock_acquire);
    //@ produce_func_lt(ticketlock_dispose);
    //@ int releaseThread = currentThread;
    /*@
    produce_lemma_function_pointer_chunk ticketlock_release_ghost_op(cohort_ticketlock_inv(cohort), localTicket, p02, obs01, pre_, post_, currentThread)() {
      assert obs_(releaseThread, ?p1, obs01);
      open pre_();
      open cohort_ticketlock_inv(cohort)(localTicket, true);
      
      assert atomic_spaces(?spaces);
      if (mem(pair(create_cohort, COHORT_INV), spaces)) {
          mem_map(pair(create_cohort, COHORT_INV), spaces, fst);
          forall_elim(map(fst, spaces), (func_gt)(ticketlock_dispose), create_cohort);
          assert false;
      }
      open_atomic_space(create_cohort, COHORT_INV);
      open COHORT_INV();
      if (mem(pair(create_cohortlock, cohortlock_inv(lock, inv, ownerIncrBox, roundsInfoId)), spaces)) {
          mem_map(pair(create_cohortlock, cohortlock_inv(lock, inv, ownerIncrBox, roundsInfoId)), spaces, fst);
          forall_elim(map(fst, spaces), (func_gt)(ticketlock_dispose), create_cohortlock);
          assert false;
      }
      match_has_at<int>(globalOwnersId);
      leak has_at(_, globalOwnersId, _, _);
      open_atomic_space(create_cohortlock, cohortlock_inv(lock, inv, ownerIncrBox, roundsInfoId));
      open cohortlock_inv(lock, inv, ownerIncrBox, roundsInfoId)();
      match_has_at_<global_round_info>(globalTicketHandle);
      match_has_at(roundsInfoId);
      leak has_at(globalTicketHandle, roundsInfoId, globalTicket, _);
      merge_fractions cohort_owner(cohort, _);
      merge_fractions cohort_held(cohort, _);
      merge_fractions cohort->_passedCount |-> _;
      merge_fractions cohort->releasing |-> _;
      
      cohort->held = false;
      cohort->releasing = false;
      cohort->owner++;
      cohort->_passedCount = passedCount;
      list<pair<void *, level> > obs1 = obs;
      if (passing) {
        assert growing_list<int>(globalOwnersId, ?globalOwners);
        growing_list_add(globalOwnersId, globalTicket);
        nth_append_r(globalOwners, {globalTicket}, 0);
        growing_list_add<void *>(releaseSignalsId, 0);
        assert growing_list<global_round_info>(roundsInfoId, ?roundsInfo);
        consuming_box_predicate incr_box(incrBoxId, oldPassedCount)
        perform_action incr() {}
        producing_box_predicate incr_box(passedCount);
        
        if (!forall(map(fst, spaces), (func_gt)(cohortlock_dispose))) {
          void *badName = not_forall(map(fst, spaces), (func_gt)(cohortlock_dispose));
          forall_elim(map(fst, spaces), (func_gt)(ticketlock_dispose), badName);
          assert false;
        }
        ghop();
        leak is_cohortlock_release_ghost_op(ghop, _, _, _, _, _, _, _);
        assert obs_(releaseThread, p1, ?obs1_);
        obs1 = obs1_;
        
        if (!forall(map(snd, obs1), (func_lt_level)(ticketlock_acquire))) {
            level badLevel = not_forall(map(snd, obs1), (func_lt_level)(ticketlock_acquire));
            forall_elim(map(snd, obs1), (func_lt_level)(cohortlock_acquire), badLevel);
            assert false;
        }
        
        open queue_info(cohort, enqueueIncrBoxId, queueListId, waiteeListId, localTicket, true, true);
        consuming_box_predicate incr_box(enqueueIncrBoxId, _)
        consuming_handle_predicate is_lower_bound(_, _)
        perform_action noop() {};
        assert ghost_list(queueListId, cons(pair(?queueHead, _), _));
        assert growing_list<void *>(waiteeListId, ?waitees);
        growing_list_add<void *>(waiteeListId, queueHead);
        nth_append_r(waitees, {queueHead}, 0);
        close queue_info(cohort, enqueueIncrBoxId, queueListId, waiteeListId, localTicket + 1, false, true);
      } else {
        open queue_info(cohort, enqueueIncrBoxId, queueListId, waiteeListId, localTicket, true, false);
        assert ghost_list(queueListId, ?queue);
        if (queue != {}) {
            assert queue == cons(pair(?queueHead, _), _);
            assert growing_list<void *>(waiteeListId, ?waitees);
            growing_list_add<void *>(waiteeListId, queueHead);
            nth_append_r(waitees, {queueHead}, 0);
        }
        close queue_info(cohort, enqueueIncrBoxId, queueListId, waiteeListId, localTicket + 1, false, false);
        assert obs01 == cons(pair(?releaseSignal, L), clientObs01);
        match_has_at<void *>(releaseSignalsId);
        leak has_at<void *>(_, releaseSignalsId, _, _);
        set_signal(releaseSignal);
        leak signal(releaseSignal, L, true);
        obs1 = tail(obs01);
        if (!forall(map(snd, obs1), (func_lt_level)(ticketlock_acquire))) {
            level badLevel = not_forall(map(snd, obs1), (func_lt_level)(ticketlock_acquire));
            forall_elim(map(snd, obs1), (func_lt_level)(cohortlock_acquire), badLevel);
            assert false;
        }
      }
      
      close cohortlock_inv(lock, inv, ownerIncrBox, roundsInfoId)();
      close_atomic_space(create_cohortlock, cohortlock_inv(lock, inv, ownerIncrBox, roundsInfoId));
      
      close COHORT_INV();
      close_atomic_space(create_cohort, COHORT_INV);
      
      close cohort_ticketlock_inv(cohort)(localTicket + 1, false);
      close post_(p1, obs1);
    };
    @*/
    /*@
    if (!forall(map(snd, clientObs01), (func_lt_level)(ticketlock_acquire))) {
        level badLevel = not_forall(map(snd, clientObs01), (func_lt_level)(ticketlock_acquire));
        forall_elim(map(snd, clientObs01), (func_lt_level)(cohortlock_acquire), badLevel);
        assert false;
    }
    @*/
    //@ close pre_();
    ticketlock_release(cohort->lock);
    //@ open post_(?p1, _);
    //@ assert obs(?p2, _);
    //@ is_ancestor_of_trans(p02, p1, p2);
    //@ is_ancestor_of_trans(p01, p02, p2);
  }
}

void cohort_dispose(cohort cohort)
//@ requires cohort(cohort, ?lock, ?inv, ?frac);
//@ ensures [frac]cohortlock(lock, inv);
//@ terminates;
{
  //@ box enqueueIncrBoxId = cohort->enqueueIncrBoxId;
  //@ int queueListId = cohort->queueListId;
  //@ box waiteeListId = cohort->waiteeListId;
  //@ box ownerSignalsId = cohort->ownerSignalsId;
  //@ box globalOwnersId = cohort->globalOwnersId;
  //@ box releaseSignalsId = cohort->releaseSignalsId;
  //@ ticketlock globalLock = cohort->cohortlock->lock;
  //@ box ownerIncrBox = lock->ownerIncrBox;
  //@ box roundsInfoId = lock->roundsInfoId;
  ticketlock_dispose(cohort->lock);
  //@ open cohort_ticketlock_inv(cohort)(?owner, ?held);
  //@ assert !held;
  //@ destroy_atomic_space();
  //@ open COHORT_INV();
  /*@
  if (cohort->passing) {
    open passing_global_owner_handle(?passingGlobalOwnerHandle);
    int globalOwner = lock->owner;
    {
      predicate pre() =
          [1/4]lock->owner |-> globalOwner &*&
          has_at(passingGlobalOwnerHandle, roundsInfoId, globalOwner, global_round_info(cohort, enqueueIncrBoxId, queueListId, waiteeListId, ?incrBoxId, ?cohortHeldIncrBoxId, ?initialClientOwner, ?initialLocalOwner)) &*&
          [frac]atomic_space(create_cohortlock, cohortlock_inv(lock, inv, ownerIncrBox, roundsInfoId)) &*&
          [1/2]cohort->held |-> false &*&
          [1/4]lock->held_ |-> true &*&
          cohort->queueListId |-> queueListId;
      predicate post() = false;
      produce_lemma_function_pointer_chunk atomic_noop_ghost_op(pre, post, currentThread)() {
          open pre();
          open_atomic_space(create_cohortlock, cohortlock_inv(lock, inv, ownerIncrBox, roundsInfoId));
          open cohortlock_inv(lock, inv, ownerIncrBox, roundsInfoId)();
          match_has_at_(passingGlobalOwnerHandle);
          merge_fractions cohort->held |-> _;
          open queue_info(cohort, enqueueIncrBoxId, queueListId, waiteeListId, _, _, _);
          assert ghost_list<pair<void *, real> >(queueListId, cons(?queueHead, _));
          open foreach(_, signal_pred(cohort));
          open signal_pred(cohort)(_);
          assert false;
      };
      close pre();
      atomic_noop();
      open post();
    }
    assert false;
  }
  @*/
  //@ open queue_info(cohort, enqueueIncrBoxId, queueListId, waiteeListId, _, _, _);
  //@ destroy_counter(&cohort->queueSize);
  free(cohort);
  //@ leak ghost_list(queueListId, ?queue) &*& foreach(queue, signal_pred(cohort));
  //@ leak growing_list<void *>(waiteeListId, _);
  //@ leak growing_list<int>(globalOwnersId, _);
  //@ leak growing_list<owner_signal_info>(ownerSignalsId, _);
  //@ leak growing_list<void *>(releaseSignalsId, _);
  //@ leak incr_box(enqueueIncrBoxId, _);
}

void cohortlock_dispose(cohortlock lock)
//@ requires cohortlock(lock, ?inv);
//@ ensures inv(_, false);
//@ terminates;
{
  ticketlock_dispose(lock->lock);
  //@ open cohortlock_ticketlock_inv(lock)(?globalOwner, false);
  //@ destroy_atomic_space();
  //@ box ownerIncrBox = lock->ownerIncrBox;
  //@ box roundsInfoId = lock->roundsInfoId;
  //@ open cohortlock_inv(lock, inv, ownerIncrBox, roundsInfoId)();
  free(lock);
  //@ leak growing_list(_, _);
  //@ leak incr_box(_, _);
}
