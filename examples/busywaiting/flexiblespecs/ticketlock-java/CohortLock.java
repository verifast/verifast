// tab_size:4

// Justus Fasse and Bart Jacobs. Expressive modular verification of termination for busy-waiting programs. 2023.

/*@

lemma void note(boolean b)
    requires b;
    ensures b;
{}

lemma void take_take<t>(int m, int n, list<t> xs)
    requires 0 <= m &*& m <= n &*& n <= length(xs);
    ensures take(m, take(n, xs)) == take(m, xs);
{
    switch (xs) {
        case nil:
        case cons(h, t):
            if (m == 0) {
            } else {
                take_take(m - 1, n - 1, t);
            }
    }
}

fixpoint int min(int x, int y) { return x < y ? x : y; }

lemma_auto(length(take(n, xs))) void length_take_<t>(int n, list<t> xs)
    requires 0 <= n;
    ensures length(take(n, xs)) == min(n, length(xs));
{
    switch (xs) {
        case nil:
        case cons(h, t):
            if (n == 0) {
            } else {
                length_take_(n - 1, t);
            }
    }
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

@*/

/*@

fixpoint int CohortLock_level_nb_dims() { return Ticketlock_level_nb_dims + 1; }

lemma_auto void cohortlock_nb_level_dims_nonneg()
    requires true;
    ensures 0 <= CohortLock_level_nb_dims;
{}

fixpoint Class CohortLock_targetClass() { return Ticketlock_targetClass; }

typedef lemma void CohortLock_wait_op(CohortLock l, int owner_, predicate() P)();
  requires l.state(?owner, ?held) &*& P();
  ensures l.state(owner, held) &*& owner == owner_ &*& held &*& P();

typedef lemma void CohortLock_wait_ghost_op(list<pathcomp> p, CohortLock l, list<int> ns, level level, int nbDegrees, predicate(int oldOwner) waitInv, int callerThread)(int owner, boolean newRound, CohortLock_wait_op *op);
  requires
    obs(callerThread, p, ?obs) &*& forall(map(snd, obs), (level_lt)(level)) == true &*&
    atomic_spaces(?spaces) &*& forall(map(fst, spaces), (is_prefix_of)(ns)) == true &*&
    is_CohortLock_wait_op(op, l, owner, ?P) &*& P() &*&
    0 <= owner &*&
    waitInv(?oldOwner) &*&
    newRound ?
      cp_lex(p, CohortLock_targetClass, {nbDegrees})
    :
      owner == oldOwner;
  ensures
    obs(callerThread, p, obs) &*&
    atomic_spaces(spaces) &*&
    is_CohortLock_wait_op(op, l, owner, P) &*& P() &*&
    call_perm_(callerThread, CohortLock_targetClass) &*& waitInv(owner);

typedef lemma void CohortLock_acquire_op(CohortLock l, int owner_, predicate() P, predicate() Q)();
  requires l.state(?owner, ?held) &*& P();
  ensures l.state(owner, true) &*& owner == owner_ &*& !held &*& Q();

typedef lemma void CohortLock_acquire_ghost_op(list<pathcomp> p, list<pair<void *, level> > obs, CohortLock l, list<int> ns, predicate(int oldOwner) waitInv, predicate(int) post, int callerThread)(int owner, CohortLock_acquire_op *op);
  requires
    obs(callerThread, p, obs) &*&
    atomic_spaces(?spaces) &*& forall(map(fst, spaces), (is_prefix_of)(ns)) == true &*&
    is_CohortLock_acquire_op(op, l, owner, ?P, ?Q) &*& P() &*& 0 <= owner &*& waitInv(_);
  ensures
    atomic_spaces(spaces) &*&
    is_CohortLock_acquire_op(op, l, owner, P, Q) &*& Q() &*&
    post(owner);

typedef lemma void CohortLock_release_op(CohortLock l, long ticket, predicate() P, predicate() Q)();
  requires l.state(?owner, ?held) &*& P();
  ensures l.state(ticket + 1, false) &*& owner == ticket &*& held &*& Q();

typedef lemma void CohortLock_release_ghost_op(CohortLock l, list<int> ns, long ticket, predicate() pre, predicate() post)(CohortLock_release_op *op);
  requires
    atomic_spaces(?spaces) &*& forall(map(fst, spaces), (is_prefix_of)(ns)) == true &*&
    is_CohortLock_release_op(op, l, ticket, ?P, ?Q) &*& P() &*& pre();
  ensures
    atomic_spaces(spaces) &*&
    is_CohortLock_release_op(op, l, ticket, P, Q) &*& Q() &*& post();

lemma void CohortLock_not_alone_elim(CohortLock this)
  requires
    [_]this.valid(?ns, ?level) &*&
    atomic_spaces(?spaces) &*& forall(map(fst, spaces), (not_is_prefix_of)(ns)) == true &*&
    this.state(?owner, ?held) &*&
    CohortLock_not_alone(this, owner - 1);
  ensures
    atomic_spaces(spaces) &*&
    CohortLock_not_alone(this, owner - 1) &*&
    this.state(owner, held) &*& held;
{
    open CohortLock_not_alone(this, owner - 1);
    open exists(?notAloneHandle);
    open this.valid(ns, level);
    if (mem(pair(append(ns, {CohortLock.NS_}), CohortLock_inv(this)), spaces)) {
        mem_map(pair(append(ns, {CohortLock.NS_}), CohortLock_inv(this)), spaces, fst);
        forall_elim(map(fst, spaces), (not_is_prefix_of)(ns), append(ns, {CohortLock.NS_}));
        take_append(length(ns), ns, {CohortLock.NS_});
        assert false;
    }
    open_atomic_space(append(ns, {CohortLock.NS_}), CohortLock_inv(this));
    open CohortLock_inv(this)();
    open this.state(owner, held);
    if (!held) {
        box roundsInfoId = this.roundsInfoId;
        match_has_at_(notAloneHandle);
        Ticketlock globalLock = this.ticketlock;
        assert globalLock.state(?globalOwner, ?globalHeld);
        if (globalHeld) {
            assert growing_list<global_round_info>(roundsInfoId, ?roundsInfo);
            assert nth(globalOwner, roundsInfo) == global_round_info(?ownerCohort, _, _, _);
            if (!ownerCohort.held_) {
                drop_append_l(length(ns), ns, {Cohort.TICKETLOCK_NS_});
                drop_append_l(length(ns), ns, {CohortLock.NS_});
                assert length(append(ns, {Cohort.TICKETLOCK_NS_})) == length(append(ns, {CohortLock.NS_}));
                assert not_is_prefix_of(append(ns, {Cohort.TICKETLOCK_NS_}), append(ns, {CohortLock.NS_})) == true;
                if (!forall(map(fst, spaces), (not_is_prefix_of)(append(ns, {Cohort.TICKETLOCK_NS_})))) {
                    list<int> badNs = not_forall(map(fst, spaces), (not_is_prefix_of)(append(ns, {Cohort.TICKETLOCK_NS_})));
                    forall_elim(map(fst, spaces), (not_is_prefix_of)(ns), badNs);
                    assert take(length(append(ns, {Cohort.TICKETLOCK_NS_})), badNs) == append(ns, {Cohort.TICKETLOCK_NS_});
                    length_take_(length(ns) + 1, badNs);
                    take_take(length(ns), length(ns) + 1, badNs);
                    take_append(length(ns), ns, {Cohort.TICKETLOCK_NS_});
                    assert is_prefix_of(ns, badNs) == true;
                    assert false;
                }
                Ticketlock_not_alone_elim(ownerCohort.ticketlock);
                assert false;
            }
        } else {
            drop_append_l(length(ns), ns, {CohortLock.TICKETLOCK_NS_});
            drop_append_l(length(ns), ns, {CohortLock.NS_});
            assert length(append(ns, {CohortLock.TICKETLOCK_NS_})) == length(append(ns, {CohortLock.NS_}));
            assert not_is_prefix_of(append(ns, {CohortLock.TICKETLOCK_NS_}), append(ns, {CohortLock.NS_})) == true;
            if (!forall(map(fst, spaces), (not_is_prefix_of)(append(ns, {CohortLock.TICKETLOCK_NS_})))) {
                list<int> badNs = not_forall(map(fst, spaces), (not_is_prefix_of)(append(ns, {CohortLock.TICKETLOCK_NS_})));
                forall_elim(map(fst, spaces), (not_is_prefix_of)(ns), badNs);
                assert take(length(append(ns, {CohortLock.TICKETLOCK_NS_})), badNs) == append(ns, {CohortLock.TICKETLOCK_NS_});
                length_take_(length(ns) + 1, badNs);
                take_take(length(ns), length(ns) + 1, badNs);
                take_append(length(ns), ns, {CohortLock.TICKETLOCK_NS_});
                assert is_prefix_of(ns, badNs) == true;
                assert false;
            }
            Ticketlock_not_alone_elim(globalLock);
            assert false;
        }
        assert false;
    }
    close CohortLock_inv(this)();
    close_atomic_space(append(ns, {CohortLock.NS_}), CohortLock_inv(this));
    close exists(notAloneHandle);
    close CohortLock_not_alone(this, owner - 1);
}

inductive client_round_info = client_round_info(Cohort ownerCohort, int ownerCohortOwner);

inductive global_round_info = global_round_info(Cohort ownerCohort, box passCountIncrBoxId, int initialClientOwner, int initialLocalOwner);

predicate not_alone_locally(boolean notAloneLocally) = true;

predicate_ctor CohortLock_inv(CohortLock lock)() =
    [1/2]lock.clientOwner |-> ?clientOwner &*&
    [1/2]lock.clientHeld |-> ?clientHeld &*&
    [_]lock.ns |-> ?ns &*&
    [_]lock.level |-> ?level &*&
    [_]lock.ticketlock |-> ?globalLock &*&
    [_]globalLock.valid(append(ns, {CohortLock.TICKETLOCK_NS_}), sublevel(level, CohortLock.LEVEL)) &*&
    globalLock.state(?owner, ?held) &*&
    [_]lock.ownerIncrBox |-> ?ownerIncrBox &*&
    [_]lock.roundsInfoId |-> ?roundsInfoId &*&
    [_]lock.clientRoundsInfoId |-> ?clientRoundsInfoId &*&
    [_]lock.notAloneListId |-> ?notAloneListId &*&
    [1/4]lock.owner |-> owner &*& 0 <= owner &*&
    incr_box(ownerIncrBox, owner) &*&
    [1/4]lock.held_ |-> held &*&
    growing_list<global_round_info>(roundsInfoId, ?roundsInfo) &*&
    length(roundsInfo) == owner + (held ? 1 : 0) &*&
    growing_list<boolean>(notAloneListId, ?notAloneList) &*&
    growing_list<client_round_info>(clientRoundsInfoId, ?clientRoundsInfo) &*&
    held ?
        nth(owner, roundsInfo) == global_round_info(?ownerCohort, ?passCountIncrBoxId, ?initialClientOwner, ?initialLocalOwner) &*&
        [_]ownerCohort.ticketlock |-> ?ownerCohortTicketlock &*&
        0 <= initialClientOwner &*& 0 <= initialLocalOwner &*&
        [1/2]ownerCohort._passing |-> true &*&
        [1/2]ownerCohort._passCount |-> ?passCount &*& 0 <= passCount &*& passCount <= Cohort.MAX_PASS_COUNT &*&
        incr_box(passCountIncrBoxId, passCount) &*&
        [1/4]ownerCohort.owner |-> ?cohortOwner &*& cohortOwner == initialLocalOwner + passCount &*&
        length(clientRoundsInfo) == clientOwner + 1 &*&
        nth(clientOwner, clientRoundsInfo) == client_round_info(ownerCohort, cohortOwner) &*&
        [_]ownerCohortTicketlock.valid(append(ns, {Cohort.TICKETLOCK_NS_}), sublevel(level, Cohort.LEVEL)) &*&
        [1/4]ownerCohort.held_ |-> ?cohortHeld &*& ownerCohortTicketlock.state(cohortOwner, cohortHeld) &*&
        clientOwner == initialClientOwner + passCount &*& clientHeld == cohortHeld &*&
        (cohortHeld ? true : Ticketlock_not_alone(ownerCohortTicketlock, cohortOwner - 1)) &*&
        length(notAloneList) == clientOwner ?
            true
        :
            length(notAloneList) == clientOwner + 1 &*& nth(clientOwner, notAloneList) == true &*&
            not_alone_locally(?notAloneLocally) &*&
            notAloneLocally ?
                Ticketlock_not_alone(ownerCohortTicketlock, cohortOwner)
            :
                Ticketlock_not_alone(globalLock, owner)
    :
        [1/4]lock.owner |-> owner &*& [1/4]lock.held_ |-> held &*& !clientHeld &*& 0 <= clientOwner &*&
        length(notAloneList) == clientOwner &*&
        clientOwner > 0 && nth(clientOwner - 1, notAloneList) ?
            Ticketlock_not_alone(globalLock, owner - 1)
        :
            true;

predicate passing_global_owner_handle(handle passingGlobalOwnerHandle) = true;

predicate_ctor Cohort_inv(Cohort cohort)() =
    [_]cohort.lock |-> ?lock &*&
    [_]lock.ns |-> ?ns &*&
    [_]atomic_space_(append(ns, {CohortLock.NS_}), CohortLock_inv(lock)) &*&
    [_]lock.level |-> ?level &*&
    [_]lock.ticketlock |-> ?globalLock &*&
    [_]lock.ownerIncrBox |-> ?ownerIncrBox &*&
    [_]lock.roundsInfoId |-> ?roundsInfoId &*&
    [_]lock.clientRoundsInfoId |-> ?clientRoundsInfoId &*&
    [_]lock.notAloneListId |-> ?notAloneListId &*&
    [_]cohort.ticketlock |-> ?ticketlock &*&
    [_]cohort.acquireSignalsId |-> ?acquireSignalsId &*&
    [_]cohort.globalOwnersId |-> ?globalOwnersId &*&
    [_]cohort.releaseSignalsId |-> ?releaseSignalsId &*&
    [1/8]cohort.owner |-> ?owner &*& 0 <= owner &*&
    [1/8]cohort.held_ |-> ?held &*&
    [1/4]cohort._passing |-> ?passing &*& (held ? true : cohort.passing |-> passing) &*&
    [1/4]cohort._passCount |-> ?passCount &*& 0 <= passCount &*& (held ? true : cohort.passCount |-> passCount) &*&
    [1/2]cohort.releasing |-> ?releasing &*&
    growing_list<void *>(acquireSignalsId, ?acquireSignals) &*& length(acquireSignals) == owner + (held ? 1 : 0) &*&
    growing_list<int>(globalOwnersId, ?globalOwners) &*& length(globalOwners) == owner + (passing || releasing ? 1 : 0) &*&
    growing_list<void *>(releaseSignalsId, ?releaseSignals) &*& length(releaseSignals) == owner + (releasing ? 1 : 0) &*&
    (held ? true : [1/4]cohort._passing |-> passing &*& [1/4]cohort._passCount |-> passCount &*& [1/8]cohort.owner |-> owner &*& [1/8]cohort.held_ |-> held &*& [1/2]cohort.releasing |-> false) &*&
    passing ?
        !releasing &*&
        [1/4]lock.owner |-> ?globalOwner &*& [1/4]lock.held_ |-> true &*&
        globalOwner == nth(owner, globalOwners) &*&
        (held ? true : globalLock.held(globalOwner)) &*&
        passing_global_owner_handle(?passingGlobalOwnerHandle) &*&
        has_at(passingGlobalOwnerHandle, roundsInfoId, globalOwner, global_round_info(cohort, ?passCountIncrBoxId, ?initialClientOwner, ?initialLocalOwner)) &*&
        owner == initialLocalOwner + passCount
    :
        ticketlock.state(owner, held) &*&
        [1/4]cohort.owner |-> owner &*&
        [1/4]cohort.held_ |-> held &*&
        [1/2]cohort._passing |-> passing &*&
        [1/2]cohort._passCount |-> passCount &*& passCount == 0 &*&
        held ?
            !releasing ?
                signal(nth(owner, acquireSignals), sublevel(level, Cohort.SIG_LEVEL), false)
            :
                signal(nth(owner, releaseSignals), sublevel(level, Cohort.SIG_LEVEL), false)
        :
            true;

predicate client_owner_info(handle globalOwnerHandle, handle globalRoundInfoHandle) = true;

predicate Cohort_held(Cohort cohort, int ticket) =
    [_]cohort.lock |-> ?lock &*&
    [_]lock.ns |-> ?ns &*&
    [_]lock.level |-> ?level &*& CohortLock_level_nb_dims <= level_subspace_nb_dims(level) &*&
    [_]lock.notAloneListId |-> ?notAloneListId &*&
    [_]lock.ownerIncrBox |-> ?ownerIncrBox &*&
    [_]lock.roundsInfoId |-> ?roundsInfoId &*&
    [_]lock.clientRoundsInfoId |-> ?clientRoundsInfoId &*&
    [_]lock.ticketlock |-> ?globalLock &*&
    [_]cohort.acquireSignalsId |-> ?acquireSignalsId &*&
    [_]cohort.globalOwnersId |-> ?globalOwnersId &*&
    [_]cohort.releaseSignalsId |-> ?releaseSignalsId &*&
    [_]cohort.ticketlock |-> ?ticketlock &*&
    ticketlock.held(?cohortTicket) &*&
    globalLock.held(?globalTicket) &*&
    client_owner_info(?globalOwnerHandle, ?globalRoundInfoHandle) &*&
    has_at(globalOwnerHandle, globalOwnersId, cohortTicket, globalTicket) &*&
    has_at(globalRoundInfoHandle, roundsInfoId, globalTicket, global_round_info(cohort, ?passCountIncrBoxId, ?initialClientOwner, ?initialLocalOwner)) &*&
    ticket == initialClientOwner + (cohortTicket - initialLocalOwner) &*&
    [1/4]cohort._passing |-> ?passing &*& cohort.passing |-> passing &*&
    [1/4]cohort._passCount |-> ?passCount &*& cohort.passCount |-> passCount &*&
    [1/8]cohort.held_ |-> true &*&
    [1/8]cohort.owner |-> cohortTicket &*&
    [1/2]cohort.releasing |-> false;

predicate CohortLock_not_alone(CohortLock lock, int owner) =
    [_]lock.notAloneListId |-> ?notAloneListId &*&
    [_]lock.valid(?ns, ?level) &*&
    exists(?notAloneHandle) &*& has_at(notAloneHandle, notAloneListId, owner, true);

@*/

final class CohortLock {
    //@ static final int NS_ = 0;
    //@ static final int TICKETLOCK_NS_ = 1;
    //@ static final list<int> LEVEL = {0};
    
    //@ list<int> ns;
    //@ level level;
    Ticketlock ticketlock;
    //@ box notAloneListId;
    //@ int owner;
    //@ box ownerIncrBox;
    //@ boolean held_;
    //@ box roundsInfoId;
    //@ box clientRoundsInfoId;
    //@ int clientOwner;
    //@ boolean clientHeld;
    
    /*@
	predicate valid(list<int> ns, level level) =
		[_]this.ns |-> ns &*&
		[_]this.level |-> level &*& CohortLock_level_nb_dims <= level_subspace_nb_dims(level) &*&
		[_]this.notAloneListId |-> ?notAloneListId &*&
		[_]this.ownerIncrBox |-> ?ownerIncrBox &*&
		[_]this.roundsInfoId |-> ?roundsInfoId &*&
		[_]this.clientRoundsInfoId |-> ?clientRoundsInfoId &*&
		[_]this.ticketlock |-> ?globalLock &*&
		[_]globalLock.valid(append(ns, {TICKETLOCK_NS_}), sublevel(level, LEVEL)) &*&
		[_]atomic_space_(append(ns, {NS_}), CohortLock_inv(this));
    @*/

    /*@
    predicate state(int owner, boolean held) =
        [1/2]this.clientOwner |-> owner &*& [1/2]this.clientHeld |-> held;
    @*/

	CohortLock()
	//@ requires exists<pair<list<int>, level> >(pair(?ns, ?level)) &*& CohortLock_level_nb_dims <= level_subspace_nb_dims(level);
	//@ ensures [_]valid(ns, level);
	//@ terminates;
	{
		//@ open exists(pair(ns, level));
		//@ this.ns = ns;
		//@ this.level = level;
		//@ this.owner = 0;
		//@ this.held_ = false;
		//@ close exists(pair(append(ns, {TICKETLOCK_NS_}), sublevel(level, LEVEL)));
		//@ assert level == level(_, cons(?levelNbDims, ?level0));
		Ticketlock ticketlock = new Ticketlock();
		this.ticketlock = ticketlock;
		//@ box notAloneListId = create_growing_list<boolean>();
		//@ this.notAloneListId = notAloneListId;
		//@ create_box ownerIncrBox = incr_box(0);
		//@ this.ownerIncrBox = ownerIncrBox;
		//@ box roundsInfoId = create_growing_list<global_round_info>();
		//@ this.roundsInfoId = roundsInfoId;
		//@ box clientRoundsInfoId = create_growing_list<client_round_info>();
		//@ this.clientRoundsInfoId = clientRoundsInfoId;
		//@ leak this.ns |-> _ &*& this.level |-> _ &*& this.ticketlock |-> _ &*& this.ownerIncrBox |-> _ &*& this.notAloneListId |-> _ &*& this.roundsInfoId |-> _ &*& this.clientRoundsInfoId |-> _;
		//@ close CohortLock_inv(this)();
		//@ create_atomic_space_(append(ns, {NS_}), CohortLock_inv(this));
	}

}

/*@

inductive cohort_leader_state =
  acquiring_state(handle acquireSignalHandle)
| passing_state(handle globalOwnerHandle, handle globalRoundInfoHandle)
| releasing_state(handle releaseSignalHandle);

@*/


final class Cohort {
    static final int MAX_PASS_COUNT = 100;
    
    //@ static final int NS_ = 2;
    //@ static final int TICKETLOCK_NS_ = 3;
    //@ static final list<int> SIG_LEVEL = {1};
    //@ static final list<int> LEVEL = {2};
    
    CohortLock lock;
    //@ real frac;
    Ticketlock ticketlock;
    boolean passing;
    int passCount;
    //@ boolean _passing;
    //@ int _passCount;
    //@ boolean releasing;
    //@ int owner;
    //@ boolean held_;
    //@ box acquireSignalsId;
    //@ box globalOwnersId;
    //@ box releaseSignalsId;

    /*@
    predicate valid(CohortLock lock) =
		[_]this.lock |-> lock &*&
		[_]lock.ns |-> ?ns &*&
		[_]lock.level |-> ?level &*& CohortLock_level_nb_dims <= level_subspace_nb_dims(level) &*&
		[_]lock.notAloneListId |-> ?notAloneListId &*&
		[_]lock.ownerIncrBox |-> ?ownerIncrBox &*&
		[_]lock.roundsInfoId |-> ?roundsInfoId &*&
		[_]lock.clientRoundsInfoId |-> ?clientRoundsInfoId &*&
		[_]lock.ticketlock |-> ?globalLock &*&
		[_]this.acquireSignalsId |-> ?acquireSignalsId &*&
		[_]this.globalOwnersId |-> ?globalOwnersId &*&
		[_]this.releaseSignalsId |-> ?releaseSignalsId &*&
		[_]this.ticketlock |-> ?ticketlock &*&
		[_]ticketlock.valid(append(ns, {Cohort.TICKETLOCK_NS_}), sublevel(level, LEVEL)) &*&
		[_]atomic_space_(append(ns, {Cohort.NS_}), Cohort_inv(this));
	@*/
	
	Cohort(CohortLock lock)
	//@ requires [_]lock.valid(?ns, ?level);
	//@ ensures [_]valid(lock);
	//@ terminates;
	{
		//@ open lock.valid(ns, level);
		//@ Ticketlock globalLock = lock.ticketlock;
		//@ box ownerIncrBox = lock.ownerIncrBox;
		//@ box roundsInfoId = lock.roundsInfoId;
		//@ box clientRoundsInfoId = lock.clientRoundsInfoId;
		this.lock = lock;
		//@ this.owner = 0;
		//@ this.held_ = false;
		this.passing = false;
		//@ this._passing = false;
		this.passCount = 0;
		//@ this._passCount = 0;
		//@ this.releasing = false;
		//@ close exists(pair(append(ns, {TICKETLOCK_NS_}), sublevel(level, LEVEL)));
		//@ assert level == level(_, cons(_, _));
		Ticketlock ticketlock = new Ticketlock();
		this.ticketlock = ticketlock;
		//@ box acquireSignalsId = create_growing_list<void *>();
		//@ this.acquireSignalsId = acquireSignalsId;
		//@ box globalOwnersId = create_growing_list<int>();
		//@ this.globalOwnersId = globalOwnersId;
		//@ box releaseSignalsId = create_growing_list<void *>();
		//@ this.releaseSignalsId = releaseSignalsId;
		//@ leak this.lock |-> _ &*& this.ticketlock |-> _ &*& this.acquireSignalsId |-> _ &*& this.globalOwnersId |-> _ &*& this.releaseSignalsId |-> _;
		//@ close Cohort_inv(this)();
		//@ create_atomic_space_(append(ns, {NS_}), Cohort_inv(this));
	}

	void acquire()
	/*@
	requires
		[_]valid(?lock) &*& [_]lock.valid(?ns, ?level) &*&
		obs(currentThread, ?p, ?obs) &*& 
		forall(map(snd, obs), (all_sublevels_lt)(CohortLock_level_nb_dims, level)) == true &*&
		is_CohortLock_wait_ghost_op(?wop, p, lock, ns, level, ?cpDegrees, ?wait_inv, currentThread) &*& 0 <= cpDegrees &*&
		is_CohortLock_acquire_ghost_op(?aop, p, obs, lock, ns, wait_inv, ?post, currentThread) &*&
		wait_inv(-1);
	@*/
	//@ ensures Cohort_held(this, ?ticket) &*& post(ticket);
	//@ terminates;
	{
	    Cohort cohort = this;
	    //@ list<int> COHORTLOCK_NS = append(ns, {CohortLock.NS_});
	    //@ list<int> COHORT_TICKETLOCK_NS = append(ns, {TICKETLOCK_NS_});
	    //@ list<int> COHORT_NS = append(ns, {NS_});
	    //@ int COHORT_NS_ = NS_;
	    //@ level LL_LEVEL = sublevel(level, Cohort.LEVEL);
	    //@ list<int> LL_LEVEL_ = Cohort.LEVEL;
	    //@ box notAloneListId = lock.notAloneListId;
		//@ box ownerIncrBox = lock.ownerIncrBox;
		//@ box roundsInfoId = lock.roundsInfoId;
		//@ box clientRoundsInfoId = lock.clientRoundsInfoId;
		Ticketlock globalLock = this.lock.ticketlock;
		//@ box acquireSignalsId = cohort.acquireSignalsId;
		//@ box globalOwnersId = cohort.globalOwnersId;
		//@ box releaseSignalsId = cohort.releaseSignalsId;
		Ticketlock ticketlock = ticketlock;
		{
		    /*@
		    predicate acquire_signal_handle(handle acquireSignalHandle);
		    predicate client_owner_handle(handle clientOwnerHandle) = true;
		    predicate old_client_owner_cohort_owner(int oldClientOwnerCohortOwner) = true;
		    predicate wait_inv_core(int oldCohortOwner, int oldClientOwner) =
		        is_CohortLock_wait_ghost_op(wop, p, lock, ns, level, cpDegrees, wait_inv, currentThread) &*&
		        oldCohortOwner == -1 ?
		            oldClientOwner == -1
		        :
		            old_client_owner_cohort_owner(?oldClientOwnerCohortOwner) &*&
		            (
		                oldClientOwner == -1 ?
		                    oldClientOwnerCohortOwner == -1
		                :
		                    client_owner_handle(?clientOwnerHandle) &*&
		                    has_at<client_round_info>(clientOwnerHandle, clientRoundsInfoId, oldClientOwner, client_round_info(cohort, oldClientOwnerCohortOwner))
		            ) &*&
		            exists<cohort_leader_state>(?oldCohortLeaderState) &*&
		            switch (oldCohortLeaderState) {
		                case acquiring_state(acquireSignalHandle): return
		                    //oldClientOwnerCohortOwner < oldCohortOwner &*&
		                    has_at(acquireSignalHandle, acquireSignalsId, oldCohortOwner, ?acquireSignal) &*&
		                    wait_perm(p, acquireSignal, sublevel(level, SIG_LEVEL), Ticketlock_targetClass) &*&
		                    call_below_perm_lex(p, ?c1, {cpDegrees}) &*& call_below_perm(p, c1) &*& Class_lt(Ticketlock_targetClass, c1) == true;
		                case passing_state(globalOwnerHandle, globalRoundInfoHandle): return
		                    has_at(globalOwnerHandle, globalOwnersId, oldCohortOwner, ?oldGlobalOwner) &*&
		                    has_at(globalRoundInfoHandle, roundsInfoId, oldGlobalOwner, global_round_info(cohort, ?passCountIncrBoxId, ?initialClientOwner, ?initialLocalOwner)) &*&
		                    oldClientOwner == initialClientOwner + (oldCohortOwner - initialLocalOwner) &*&
		                    oldClientOwnerCohortOwner == oldCohortOwner &*&
		                    call_below_perm(p, ?c1) &*& Class_lt(Ticketlock_targetClass, c1) == true;
		                case releasing_state(releaseSignalHandle): return
		                    //oldClientOwnerCohortOwner <= oldCohortOwner &*&
		                    has_at(releaseSignalHandle, releaseSignalsId, oldCohortOwner, ?releaseSignal) &*&
		                    wait_perm(p, releaseSignal, sublevel(level, SIG_LEVEL), Ticketlock_targetClass);
		            };
		    predicate wait_inv_(int oldCohortOwner) =
		        [_]this.lock |-> lock &*&
		        [_]this.ticketlock |-> ticketlock &*& [_]ticketlock.valid(COHORT_TICKETLOCK_NS, LL_LEVEL) &*&
		        [_]lock.ns |-> ns &*&
		        [_]lock.level |-> level &*&
		        [_]lock.notAloneListId |-> notAloneListId &*&
		        [_]lock.roundsInfoId |-> roundsInfoId &*&
		        [_]lock.clientRoundsInfoId |-> clientRoundsInfoId &*&
		        [_]this.acquireSignalsId |-> acquireSignalsId &*&
		        [_]this.globalOwnersId |-> globalOwnersId &*&
		        [_]this.releaseSignalsId |-> releaseSignalsId &*&
		        [_]atomic_space_(append(ns, {NS_}), Cohort_inv(this)) &*&
		        is_CohortLock_acquire_ghost_op(aop, p, obs, lock, ns, wait_inv, post, currentThread) &*&
		        wait_inv(?oldClientOwner) &*&
		        wait_inv_core(oldCohortOwner, oldClientOwner);
		    predicate post_(int ticket) =
		        [1/4]cohort._passing |-> ?passing &*& cohort.passing |-> passing &*&
		        [1/4]cohort._passCount |-> ?passCount &*& cohort.passCount |-> passCount &*&
		        [1/8]cohort.held_ |-> true &*&
		        [1/8]cohort.owner |-> ticket &*&
		        [1/2]cohort.releasing |-> false &*&
		        passing ?
		            post(?clientOwner) &*&
		            globalLock.held(?globalOwner) &*&
		            client_owner_info(?globalOwnerHandle, ?globalRoundInfoHandle) &*&
		            has_at(globalOwnerHandle, globalOwnersId, ticket, globalOwner) &*&
		            has_at(globalRoundInfoHandle, roundsInfoId, globalOwner, global_round_info(cohort, ?passCountIncrBoxId, ?initialClientOwner, ?initialLocalOwner)) &*&
		            clientOwner == initialClientOwner + (ticket - initialLocalOwner)
		        :
		            obs(currentThread, ?p1, cons(pair(?acquireSignal, sublevel(level, SIG_LEVEL)), obs)) &*&
		            wait_inv(_) &*&
		            is_CohortLock_acquire_ghost_op(aop, p, obs, lock, ns, wait_inv, post, currentThread);
		    @*/
		    /*@
		    produce_lemma_function_pointer_chunk Ticketlock_wait_ghost_op(p, ticketlock, append(ns, {TICKETLOCK_NS_}), LL_LEVEL, cpDegrees + 1, wait_inv_, currentThread)(cohortOwner, newRound, op) {
		        assert atomic_spaces(?spaces);
		        assert obs(_, p, ?obs1);
		        open wait_inv_(?oldCohortOwner);
		        open wait_inv_core(oldCohortOwner, ?oldClientOwner);
		        
		        if (!forall(map(snd, obs1), (level_lt)(sublevel(level, SIG_LEVEL)))) {
		            level badLevel = not_forall(map(snd, obs1), (level_lt)(sublevel(level, SIG_LEVEL)));
		            forall_elim(map(snd, obs1), (level_lt)(LL_LEVEL), badLevel);
		            level_lt_append(level, SIG_LEVEL, Cohort.LEVEL);
		            level_lt_trans(sublevel(level, SIG_LEVEL), LL_LEVEL, badLevel);
		            assert false;
		        }
		        if (!forall(map(fst, spaces), (is_prefix_of)(ns))) {
		            list<int> badName = not_forall(map(fst, spaces), (is_prefix_of)(ns));
		            forall_elim(map(fst, spaces), (is_prefix_of)(append(ns, {TICKETLOCK_NS_})), badName);
		            length_take_(length(ns) + 1, badName);
		            append_drop_take(badName, length(append(ns, {TICKETLOCK_NS_})));
		            assert badName == append(append(ns, {TICKETLOCK_NS_}), drop(length(ns) + 1, badName));
		            append_assoc(ns, {TICKETLOCK_NS_}, drop(length(ns) + 1, badName));
		            take_append(length(ns), ns, cons(TICKETLOCK_NS_, drop(length(ns) + 1, badName)));
		            assert false;
		        }
		        if (!forall(map(snd, obs1), (level_lt)(level))) {
		            level badLevel = not_forall(map(snd, obs1), (level_lt)(level));
		            forall_elim(map(snd, obs1), (level_lt)(LL_LEVEL), badLevel);
		            level_lt_append(level, {}, LL_LEVEL_);
		            level_lt_trans(level, LL_LEVEL, badLevel);
		            assert false;
		        }
		        
		        if (mem(pair(COHORTLOCK_NS, CohortLock_inv(lock)), spaces)) {
		            mem_map(pair(COHORTLOCK_NS, CohortLock_inv(lock)), spaces, fst);
		            drop_append(ns, {TICKETLOCK_NS_});
		            drop_append(ns, {CohortLock.NS_});
		            forall_elim(map(fst, spaces), (is_prefix_of)(append(ns, {TICKETLOCK_NS_})), COHORTLOCK_NS);
		            assert false;
		        }
		        drop_append(ns, {NS_});
		        drop_append(ns, {CohortLock.NS_});
		        if (mem(pair(COHORT_NS, Cohort_inv(this)), spaces)) {
		            mem_map(pair(COHORT_NS, Cohort_inv(this)), spaces, fst);
		            forall_elim(map(fst, spaces), (is_prefix_of)(append(ns, {TICKETLOCK_NS_})), COHORT_NS);
		            assert false;
		        }
		        open_atomic_space(COHORT_NS, Cohort_inv(this));
		        open Cohort_inv(this)();
		        
		        boolean usedNotAloneToken = false;
		        
		        if (newRound) {
		            open cp_lex(p, Ticketlock_targetClass, {cpDegrees + 1});
		            if (oldCohortOwner == -1) {
		                close old_client_owner_cohort_owner(-1);
		            } else {
		                open exists<cohort_leader_state>(?oldCohortLeaderState);
		                switch (oldCohortLeaderState) {
		                    case acquiring_state(acquireSignalHandle):
		                        leak has_at<void *>(acquireSignalHandle, acquireSignalsId, oldCohortOwner, ?acquireSignal);
		                        leak wait_perm(p, acquireSignal, sublevel(level, SIG_LEVEL), Ticketlock_targetClass);
		                        leak call_below_perm_lex(p, _, {cpDegrees});
		                        leak call_below_perm(p, _);
		                    case passing_state(globalOwnerHandle, globalRoundInfoHandle):
		                        leak has_at<int>(globalOwnerHandle, globalOwnersId, oldCohortOwner, ?oldGlobalOwner);
		                        leak has_at<global_round_info>(globalRoundInfoHandle, roundsInfoId, oldGlobalOwner, _);
		                        leak call_below_perm(p, _);
		                        is_ancestor_of_refl(p);
		                    case releasing_state(releaseSignalHandle):
		                        leak has_at<void *>(releaseSignalHandle, releaseSignalsId, oldCohortOwner, ?releaseSignal);
		                        leak wait_perm(p, releaseSignal, sublevel(level, SIG_LEVEL), Ticketlock_targetClass);
		                }
		            }
		            
		            if (!cohort._passing && !cohort.releasing) {
		                op();
		                handle acquireSignalHandle = create_has_at<void *>(acquireSignalsId, cohortOwner);
		                assert has_at<void *>(acquireSignalHandle, acquireSignalsId, cohortOwner, ?acquireSignal);
		                call_below_perm_lex_weaken_multi(2, 1, {cpDegrees});
		                open call_below_perms_lex(1, _, _, _);
		                open call_below_perms(2, _, _);
		                open call_below_perms(1, _, _);
		                create_wait_perm(acquireSignal, sublevel(level, SIG_LEVEL), Ticketlock_targetClass);
		                is_ancestor_of_refl(p);
		                wait(acquireSignal);
		                close exists(acquiring_state(acquireSignalHandle));
		            } else if (cohort._passing) {
		                open old_client_owner_cohort_owner(?oldClientOwnerCohortOwner);
		                
		                call_below_perm_lex_weaken_multi(1, 1, {cpDegrees});
		                open call_below_perms_lex(1, _, _, _);
		                open call_below_perms_lex(0, _, _, _);
		                open call_below_perms(1, _, _);
		                open call_below_perms(0, _, _);
		                is_prefix_of_append(ns, {}, {COHORT_NS_});
		                
		                open_atomic_space(COHORTLOCK_NS, CohortLock_inv(lock));
		                open CohortLock_inv(lock)();
		                assert passing_global_owner_handle(?passingGlobalOwnerHandle);
		                match_has_at_<global_round_info>(passingGlobalOwnerHandle);
		                merge_fractions cohort.owner |-> _;
		                merge_fractions cohort.held_ |-> _;
		                merge_fractions cohort.ticketlock |-> _;
		                op();
		                assert [_]lock.clientOwner |-> ?clientOwner;
		                if (oldClientOwner != -1) {
		                    open client_owner_handle(?clientOwnerHandle);
		                    match_has_at_<client_round_info>(clientOwnerHandle);
		                    leak has_at<client_round_info>(clientOwnerHandle, _, _, _);
		                }
		                {
		                    predicate P_() = [1/2]lock.clientOwner |-> clientOwner &*& [1/2]lock.clientHeld |-> true;
		                    produce_lemma_function_pointer_chunk CohortLock_wait_op(lock, clientOwner, P_)() {
		                        open P_();
		                        open lock.state(_, _);
		                        close lock.state(clientOwner, true);
		                        close P_();
		                    } {
		                        close P_();
		                        assert is_CohortLock_wait_op(?op_, _, _, _);
		                        close cp_lex(p, CohortLock_targetClass, {cpDegrees});
    		                    wop(clientOwner, newRound, op_);
    		                    open P_();
    		                }
		                }
		                close old_client_owner_cohort_owner(cohortOwner);
		                handle clientOwnerHandle = create_has_at<client_round_info>(clientRoundsInfoId, clientOwner);
		                close client_owner_handle(clientOwnerHandle);
		                handle globalOwnerHandle = create_has_at<int>(globalOwnersId, cohortOwner);
		                assert has_at<int>(globalOwnerHandle, globalOwnersId, cohortOwner, ?globalOwner);
		                handle globalRoundInfoHandle = create_has_at<global_round_info>(roundsInfoId, globalOwner);
		                close exists<cohort_leader_state>(passing_state(globalOwnerHandle, globalRoundInfoHandle));
		                
		                close CohortLock_inv(lock)();
		                close_atomic_space(COHORTLOCK_NS, CohortLock_inv(lock));
		            } else {
		                assert [_]cohort.releasing |-> true;
    		            op();
		                handle releaseSignalHandle = create_has_at<void *>(releaseSignalsId, cohortOwner);
		                assert has_at<void *>(releaseSignalHandle, releaseSignalsId, cohortOwner, ?releaseSignal);
		                call_below_perm_lex_weaken_multi(1, 0, {cpDegrees});
		                open call_below_perms(1, _, _);
		                create_wait_perm(releaseSignal, sublevel(level, SIG_LEVEL), Ticketlock_targetClass);
		                is_ancestor_of_refl(p);
		                wait(releaseSignal);
		                close exists<cohort_leader_state>(releasing_state(releaseSignalHandle));
		            }
		            
		        } else {
		            assert cohortOwner == oldCohortOwner;
		        
		            assert old_client_owner_cohort_owner(?oldClientOwnerCohortOwner);

		            if (!cohort._passing && !cohort.releasing) {
		                op();
		                open exists<cohort_leader_state>(?oldCohortLeaderState);
		                switch (oldCohortLeaderState) {
		                    case acquiring_state(acquireSignalHandle):
		                        assert has_at<void *>(acquireSignalHandle, acquireSignalsId, oldCohortOwner, ?acquireSignal);
		                        match_has_at_<void *>(acquireSignalHandle);
		                        is_ancestor_of_refl(p);
		                        wait(acquireSignal);
		                        close exists(oldCohortLeaderState);
		                    case passing_state(globalOwnerHandle, globalRoundInfoHandle):
		                        match_has_at_<int>(globalOwnerHandle);
		                        assert false;
		                    case releasing_state(releaseSignalHandle):
		                        match_has_at_<void *>(releaseSignalHandle);
		                        assert false;
		                }
		            } else if (cohort._passing) {
		                assert COHORT_NS != COHORTLOCK_NS;
		                open_atomic_space(COHORTLOCK_NS, CohortLock_inv(lock));
		                open CohortLock_inv(lock)();
                        assert passing_global_owner_handle(?passingGlobalOwnerHandle);
                        match_has_at_<global_round_info>(passingGlobalOwnerHandle);
                        merge_fractions cohort.owner |-> _;
                        merge_fractions cohort.held_ |-> _;
                        merge_fractions cohort.ticketlock |-> _;
		                
		                op();
		                
		                open old_client_owner_cohort_owner(_);
		                if (oldClientOwner != -1) {
		                    open client_owner_handle(?clientOwnerHandle);
		                    match_has_at_<client_round_info>(clientOwnerHandle);
		                    leak has_at(clientOwnerHandle, clientRoundsInfoId, oldClientOwner, _);
		                }
		                
		                open exists<cohort_leader_state>(?oldCohortLeaderState);
		                switch (oldCohortLeaderState) {
		                    case acquiring_state(acquireSignalHandle):
		                        leak has_at<void *>(acquireSignalHandle, acquireSignalsId, oldCohortOwner, ?acquireSignal);
		                        leak wait_perm(p, acquireSignal, sublevel(level, SIG_LEVEL), _);
		                        handle globalOwnerHandle = create_has_at<int>(globalOwnersId, cohortOwner);
		                        assert has_at(globalOwnerHandle, globalOwnersId, cohortOwner, ?globalOwner);
		                        handle globalRoundInfoHandle = create_has_at<global_round_info>(roundsInfoId, globalOwner);
		                        close exists(passing_state(globalOwnerHandle, globalRoundInfoHandle));
		                    case passing_state(globalOwnerHandle, globalRoundInfoHandle):
		                        match_has_at_<int>(globalOwnerHandle);
		                        match_has_at_<global_round_info>(globalRoundInfoHandle);
		                        assert [_]lock.clientOwner |-> ?clientOwner &*& [_]lock.clientHeld |-> ?clientHeld;
		                        assert oldClientOwner == clientOwner;
		                        close exists(oldCohortLeaderState);
		                    case releasing_state(releaseSignalHandle):
		                        match_has_at_<void *>(releaseSignalHandle);
		                        
		                        assert false;
		                }
		                is_prefix_of_append(ns, {}, {TICKETLOCK_NS_});
		                assert [_]lock.clientOwner |-> ?clientOwner;
		                {
		                    predicate P_() = [1/2]lock.clientOwner |-> clientOwner &*& [1/2]lock.clientHeld |-> true;
		                    produce_lemma_function_pointer_chunk CohortLock_wait_op(lock, clientOwner, P_)() {
		                        open P_();
		                        open lock.state(_, _);
		                        close lock.state(clientOwner, true);
		                        close P_();
		                    } {
		                        close P_();
		                        assert is_CohortLock_wait_op(?op_, _, _, _);
		                        if (clientOwner != oldClientOwner)
		                            close cp_lex(p, CohortLock_targetClass, {cpDegrees});
    		                    wop(clientOwner, clientOwner != oldClientOwner, op_);
    		                    open P_();
    		                }
		                }
		                
		                handle newClientOwnerHandle = create_has_at<client_round_info>(clientRoundsInfoId, clientOwner);
		                close client_owner_handle(newClientOwnerHandle);
		                close old_client_owner_cohort_owner(cohortOwner);
		                
		                close CohortLock_inv(lock)();
		                close_atomic_space(COHORTLOCK_NS, CohortLock_inv(lock));
		            } else {
		                op();
		                assert [_]cohort.releasing |-> true;
		                open exists<cohort_leader_state>(?oldCohortLeaderState);
		                switch (oldCohortLeaderState) {
		                    case acquiring_state(acquireSignalHandle):
		                        leak has_at<void *>(acquireSignalHandle, acquireSignalsId, oldCohortOwner, ?acquireSignal);
		                        leak wait_perm(p, acquireSignal, sublevel(level, SIG_LEVEL), _);
		                        handle releaseSignalHandle = create_has_at(releaseSignalsId, cohortOwner);
		                        assert has_at<void *>(releaseSignalHandle, releaseSignalsId, cohortOwner, ?releaseSignal);
		                        create_wait_perm(releaseSignal, sublevel(level, SIG_LEVEL), Ticketlock_targetClass);
		                        close exists(releasing_state(releaseSignalHandle));
		                        is_ancestor_of_refl(p);
		                        wait(releaseSignal);
		                        leak call_below_perm_lex(_, _, _);
		                    case passing_state(globalOwnerHandle, globalRoundInfoHandle):
		                        leak has_at<int>(globalOwnerHandle, globalOwnersId, oldCohortOwner, ?oldGlobalOwner);
		                        leak has_at<global_round_info>(globalRoundInfoHandle, roundsInfoId, oldGlobalOwner, _);
		                        handle releaseSignalHandle = create_has_at(releaseSignalsId, cohortOwner);
		                        assert has_at(releaseSignalHandle, releaseSignalsId, cohortOwner, ?releaseSignal);
		                        create_wait_perm(releaseSignal, sublevel(level, SIG_LEVEL), Ticketlock_targetClass);
		                        close exists(releasing_state(releaseSignalHandle));
		                        is_ancestor_of_refl(p);
		                        wait(releaseSignal);
		                    case releasing_state(releaseSignalHandle):
		                        assert has_at<void *>(releaseSignalHandle, releaseSignalsId, oldCohortOwner, ?releaseSignal);
		                        match_has_at_<void *>(releaseSignalHandle);
		                        if (!forall(map(snd, obs1), (level_lt)(sublevel(level, SIG_LEVEL)))) {
		                            level badLevel = not_forall(map(snd, obs1), (level_lt)(sublevel(level, SIG_LEVEL)));
		                            forall_elim(map(snd, obs1), (level_lt)(LL_LEVEL), badLevel);
		                            level_lt_append(level, SIG_LEVEL, LL_LEVEL_);
		                            level_lt_trans(sublevel(level, SIG_LEVEL), LL_LEVEL, badLevel);
		                            assert false;
		                        }
		                        is_ancestor_of_refl(p);
		                        wait(releaseSignal);
		                        close exists(oldCohortLeaderState);
		                }
		                
		            }
		        }
		        
		        close Cohort_inv(this)();
		        close_atomic_space(COHORT_NS, Cohort_inv(this));
		        assert wait_inv(?newClientOwner);
		        close wait_inv_core(cohortOwner, newClientOwner);
		        close wait_inv_(cohortOwner);
		    };
		    @*/
		    /*@
		    produce_lemma_function_pointer_chunk ticketlock_acquire_ghost_op(obs, append(ns, {TICKETLOCK_NS_}), LL_LEVEL, cohort_ticketlock_inv(cohort), wait_inv_, post_, currentThread)() {
		        assert atomic_spaces(?spaces);
		        assert obs_(?callerThread, ?p1, obs);
		        open cohort_ticketlock_inv(cohort)(?cohortOwner, false);
		        open wait_inv_(_, _, ?p0);
		        leak wait_inv_core(_, _, _, ?oldClientOwner, ?oldClientf, ?oldClientp);
		        is_ancestor_of_trans(oldClientp, p0, p1);
		        
		        if (!forall(map(fst, spaces), (is_prefix_of)(ns))) {
		            list<void *> badName = not_forall(map(fst, spaces), (is_prefix_of)(ns));
		            forall_elim(map(fst, spaces), (is_prefix_of)(append(ns, {TICKETLOCK_NS_})), badName);
		            append_drop_take(badName, length(append(ns, {TICKETLOCK_NS_})));
		            assert badName == append(append(ns, {TICKETLOCK_NS_}), drop(length(ns) + 1, badName));
		            append_assoc(ns, {TICKETLOCK_NS_}, drop(length(ns) + 1, badName));
		            take_append(length(ns), ns, cons(TICKETLOCK_NS_, drop(length(ns) + 1, badName)));
		            assert false;
		        }
		        if (mem(pair(COHORTLOCK_NS, COHORTLOCK_INV), spaces)) {
		            mem_map(pair(COHORTLOCK_NS, COHORTLOCK_INV), spaces, fst);
		            forall_elim(map(fst, spaces), (is_prefix_of)(append(ns, {TICKETLOCK_NS_})), COHORTLOCK_NS);
		            assert false;
		        }
		        drop_append(length(ns), ns, {COHORT_NS_});
		        drop_append(length(ns), ns, {COHORTLOCK_NS_});
		        if (mem(pair(COHORT_NS, COHORT_INV), spaces)) {
		            mem_map(pair(COHORT_NS, COHORT_INV), spaces, fst);
		            forall_elim(map(fst, spaces), (is_prefix_of)(append(ns, {TICKETLOCK_NS_})), COHORT_NS);
		            assert false;
		        }
		        open_atomic_space(COHORT_NS, COHORT_INV);
		        open COHORT_INV();
		        
		        assert growing_list<void *>(acquireSignalsId, ?acquireSignals);
		        void *acquireSignal = create_signal();
		        growing_list_add(acquireSignalsId, acquireSignal);
		        nth_append_r(acquireSignals, {acquireSignal}, 0);
		        
		        if (cohort._passing) {
		            leak signal_uninit(acquireSignal);
		            open_atomic_space(COHORTLOCK_NS, COHORTLOCK_INV);
		            open COHORTLOCK_INV();
		            assert passing_global_owner_handle(?passingGlobalOwnerHandle);
		            match_has_at_<global_round_info>(passingGlobalOwnerHandle);
		            merge_fractions cohort.owner |-> _;
		            merge_fractions cohort.held |-> _;
		            assert inv(?clientOwner, false);
		            leak ticketlock_not_alone(cohortIdentity, cohortOwner);
		        
		            cohort.held = true;
		            
		            is_prefix_of_append(ns, {}, {COHORTLOCK_NS_});
		            is_prefix_of_append(ns, {}, {COHORT_NS_});
		            aop();
		            leak is_cohortlock_acquire_ghost_op(_, _, _, _, _, _, _, _);
		            
		            handle globalOwnerHandle = create_has_at<int>(globalOwnersId, cohortOwner);
		            assert has_at<int>(globalOwnerHandle, globalOwnersId, cohortOwner, ?globalOwner);
		            handle globalRoundInfoId = create_has_at<global_round_info>(roundsInfoId, globalOwner);
		            close client_owner_info(globalOwnerHandle, globalRoundInfoId);
		            
		            close COHORTLOCK_INV();
		            close_atomic_space(COHORTLOCK_NS, COHORTLOCK_INV);
		        } else {
		            cohort.held = true;
		            
		            init_signal(acquireSignal, sublevel(level, SIG_LEVEL));
		        }
		        
		        close COHORT_INV();
		        close_atomic_space(COHORT_NS, COHORT_INV);
		        
		        close cohort_ticketlock_inv(cohort)(cohortOwner, true);
		        close post_(cohortOwner);
		    };
		    @*/
		    //@ is_ancestor_of_refl(p);
		    //@ assert wait_inv(-1, ?clientf, p);
		    //@ close wait_inv_core(-1, 0, p, -1, clientf, p);
		    //@ close wait_inv_(-1, 0, p);
		    /*@
		    if (!forall(map(snd, obs), (all_sublevels_lt)(ticketlock_nb_level_dims, LL_LEVEL))) {
		        level badLevel = not_forall(map(snd, obs), (all_sublevels_lt)(ticketlock_nb_level_dims, LL_LEVEL));
		        forall_elim(map(snd, obs), (all_sublevels_lt)(cohortlock_nb_level_dims, level), badLevel);
		        all_sublevels_lt_append(cohortlock_nb_level_dims, level, badLevel, ticketlock_nb_level_dims, LL_LEVEL_);
		        assert false;
		    }
		    @*/
		    ticketlock_acquire(ticketlock);
		    //@ open post_(?ticket);
		}
		if (!cohort.passing) {
		    //@ assert obs(?p1, cons(pair(?acquireSignal, sublevel(level, SIG_LEVEL)), obs));
		    {
				/*@
				predicate wait_inv_(int oldGlobalOwner, void *oldf, list<pathcomp> oldp) = true;
				predicate post_(int globalTicket) = true;
				@*/
				/*@
				produce_lemma_function_pointer_chunk ticketlock_wait_ghost_op(append(ns, {CohortLock.TICKETLOCK_NS_}), sublevel(level, CohortLock.LEVEL), cohortlock_ticketlock_inv(lock), lockIdentity, wait_inv_, currentThread, cpDegrees + 1)(f_) {
				    
				};
				@*/
				/*@
				produce_lemma_function_pointer_chunk ticketlock_acquire_ghost_op(cons(pair(acquireSignal, sublevel(level, SIG_LEVEL)), obs), append(ns, {CohortLock.TICKETLOCK_NS_}), sublevel(level, CohortLock.LEVEL), cohortlock_ticketlock_inv, wait_inv_, post_, currentThread)() {
				};
				@*/
				//@ assert level == level(_, cons(?maxLength, ?level0));
				//@ lex0_subspace_lt_append(level0, CohortLock.LEVEL, SIG_LEVEL);
				/*@
				if (!forall(map(snd, obs), (all_sublevels_lt)(ticketlock_nb_level_dims, sublevel(level, CohortLock.LEVEL)))) {
				    level badLevel = not_forall(map(snd, obs), (all_sublevels_lt)(ticketlock_nb_level_dims, sublevel(level, CohortLock.LEVEL)));
				    forall_elim(map(snd, obs), (all_sublevels_lt)(cohortlock_nb_level_dims, level), badLevel);
				    all_sublevels_lt_append(cohortlock_nb_level_dims, level, badLevel, ticketlock_nb_level_dims, CohortLock.LEVEL);
				    assert false;
				}
				@*/
				//@ close wait_inv(-1, 0, p1);
				ticketlock_acquire(globalLock);
				//@ open post_(?globalTicket);
			}
		}
		//@ close cohortlock_held(cohort, lock, ns, level, inv, identity, frac, f, _);
	}

	boolean alone()
	//@ requires [_]valid(?lock) &*& [_]lock.valid(?ns, ?level) &*& Cohort_held(this, ?owner);
	//@ ensures Cohort_held(this, owner) &*& result ? true : CohortLock_not_alone(lock, owner + 1);
	{
		return lock.ticketlock.alone() && (ticketlock.alone() || passCount < MAX_PASS_COUNT);
	}

	void release()
	/*@
	requires
	    [_]valid(?lock) &*& [_]lock.valid(?ns, ?level) &*&
	    Cohort_held(this, ?ticket) &*& is_CohortLock_release_ghost_op(?ghop, lock, ns, ticket, ?pre, ?post) &*& pre();
	@*/
	//@ ensures post();
	//@ terminates;
	{
		if (passing = (!ticketlock.alone() && passCount < MAX_PASS_COUNT)) {
		    passCount++;
		} else {
		    passCount = 0;
		    lock.ticketlock.release();
		}
		ticketlock.release();
	}

}
