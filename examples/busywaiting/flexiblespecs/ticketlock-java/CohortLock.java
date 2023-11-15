// tab_size:4

// Justus Fasse and Bart Jacobs. Expressive modular verification of termination for busy-waiting programs. 2023.

/*@

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
    [1/2]lock.notAloneLocally |-> ?notAloneLocally &*&
    [3/4]lock.owner |-> owner &*& 0 <= owner &*&
    incr_box(ownerIncrBox, owner) &*&
    [3/4]lock.held_ |-> held &*&
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
            notAloneLocally ?
                Ticketlock_not_alone(ownerCohortTicketlock, cohortOwner) &*& passCount < Cohort.MAX_PASS_COUNT
            :
                Ticketlock_not_alone(globalLock, owner)
    :
        length(clientRoundsInfo) == clientOwner &*&
        [1/2]lock.notAloneLocally |-> _ &*&
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
    [5/8]cohort.owner |-> ?owner &*& 0 <= owner &*&
    [5/8]cohort.held_ |-> ?held &*&
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
        (held ? true : [1/2]lock.notAloneLocally |-> _ &*& globalLock.held(globalOwner)) &*&
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
    has_at<int>(globalOwnerHandle, globalOwnersId, cohortTicket, globalTicket) &*&
    has_at(globalRoundInfoHandle, roundsInfoId, globalTicket, global_round_info(cohort, ?passCountIncrBoxId, ?initialClientOwner, ?initialLocalOwner)) &*&
    ticket == initialClientOwner + (cohortTicket - initialLocalOwner) &*&
    [1/4]cohort._passing |-> true &*& cohort.passing |-> _ &*&
    [1/4]cohort._passCount |-> ?passCount &*& cohort.passCount |-> passCount &*&
    [1/8]cohort.held_ |-> true &*&
    [1/8]cohort.owner |-> cohortTicket &*&
    [1/2]lock.notAloneLocally |-> _ &*&
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
    //@ boolean notAloneLocally;
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
	//@ ensures [_]valid(ns, level) &*& state(0, false);
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
		forall(map(snd, obs), (level_subspace_lt)(level)) == true &*&
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
	    //@ list<int> TL_LEVEL_ = CohortLock.LEVEL;
	    //@ level TL_LEVEL = sublevel(level, TL_LEVEL_);
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
		        [_]lock.ticketlock |-> globalLock &*&
		        [_]lock.notAloneListId |-> notAloneListId &*&
		        [_]lock.roundsInfoId |-> roundsInfoId &*&
		        [_]lock.clientRoundsInfoId |-> clientRoundsInfoId &*&
		        [_]this.acquireSignalsId |-> acquireSignalsId &*&
		        [_]this.globalOwnersId |-> globalOwnersId &*&
		        [_]this.releaseSignalsId |-> releaseSignalsId &*&
		        [_]atomic_space_(append(ns, {NS_}), Cohort_inv(this)) &*&
		        is_CohortLock_wait_ghost_op(wop, p, lock, ns, level, cpDegrees, wait_inv, currentThread) &*&
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
		            [1/2]lock.notAloneLocally |-> _ &*&
		            post(?clientOwner) &*&
		            globalLock.held(?globalOwner) &*&
		            client_owner_info(?globalOwnerHandle, ?globalRoundInfoHandle) &*&
		            has_at<int>(globalOwnerHandle, globalOwnersId, ticket, globalOwner) &*&
		            has_at(globalRoundInfoHandle, roundsInfoId, globalOwner, global_round_info(cohort, ?passCountIncrBoxId, ?initialClientOwner, ?initialLocalOwner)) &*&
		            clientOwner == initialClientOwner + (ticket - initialLocalOwner)
		        :
		            obs(currentThread, p, cons(pair(?acquireSignal, sublevel(level, SIG_LEVEL)), obs)) &*&
		            has_at(_, acquireSignalsId, ticket, acquireSignal) &*&
		            wait_inv(_) &*&
    		        is_CohortLock_wait_ghost_op(wop, p, lock, ns, level, cpDegrees, wait_inv, currentThread) &*&
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
		    produce_lemma_function_pointer_chunk Ticketlock_acquire_ghost_op(p, obs, ticketlock, append(ns, {TICKETLOCK_NS_}), wait_inv_, post_, currentThread)(cohortOwner, op) {
		        assert atomic_spaces(?spaces);
		        assert obs(?callerThread, p, obs);
		        open wait_inv_(_);
		        leak wait_inv_core(_, ?oldClientOwner);
		        
		        if (!forall(map(fst, spaces), (is_prefix_of)(ns))) {
		            list<int> badName = not_forall(map(fst, spaces), (is_prefix_of)(ns));
		            forall_elim(map(fst, spaces), (is_prefix_of)(append(ns, {TICKETLOCK_NS_})), badName);
		            append_drop_take(badName, length(append(ns, {TICKETLOCK_NS_})));
		            assert badName == append(append(ns, {TICKETLOCK_NS_}), drop(length(ns) + 1, badName));
		            append_assoc(ns, {TICKETLOCK_NS_}, drop(length(ns) + 1, badName));
		            take_append(length(ns), ns, cons(TICKETLOCK_NS_, drop(length(ns) + 1, badName)));
		            assert false;
		        }
		        if (mem(pair(COHORTLOCK_NS, CohortLock_inv(lock)), spaces)) {
		            mem_map(pair(COHORTLOCK_NS, CohortLock_inv(lock)), spaces, fst);
		            forall_elim(map(fst, spaces), (is_prefix_of)(append(ns, {TICKETLOCK_NS_})), COHORTLOCK_NS);
		            assert false;
		        }
		        drop_append(ns, {COHORT_NS_});
		        drop_append(ns, {CohortLock.NS_});
		        if (mem(pair(COHORT_NS, Cohort_inv(this)), spaces)) {
		            mem_map(pair(COHORT_NS, Cohort_inv(this)), spaces, fst);
		            forall_elim(map(fst, spaces), (is_prefix_of)(append(ns, {TICKETLOCK_NS_})), COHORT_NS);
		            assert false;
		        }
		        open_atomic_space(COHORT_NS, Cohort_inv(this));
		        open Cohort_inv(this)();
		        
		        assert growing_list<void *>(acquireSignalsId, ?acquireSignals);
		        void *acquireSignal = create_signal();
		        growing_list_add(acquireSignalsId, acquireSignal);
		        nth_append_r(acquireSignals, {acquireSignal}, 0);
		        
		        if (cohort._passing) {
		            leak signal_uninit(acquireSignal);
		            open_atomic_space(COHORTLOCK_NS, CohortLock_inv(lock));
		            open CohortLock_inv(lock)();
		            assert passing_global_owner_handle(?passingGlobalOwnerHandle);
		            match_has_at_<global_round_info>(passingGlobalOwnerHandle);
		            merge_fractions cohort.owner |-> _;
		            merge_fractions cohort.held_ |-> _;
		            merge_fractions cohort.ticketlock |-> _;
		            assert [_]lock.clientOwner |-> ?clientOwner;
		            
		            op();
		            
		            cohort.held_ = true;
		            
		            is_prefix_of_append(ns, {}, {CohortLock.NS_});
		            is_prefix_of_append(ns, {}, {COHORT_NS_});
		            {
		                predicate P_() = [1/2]lock.clientOwner |-> clientOwner &*& [1/2]lock.clientHeld |-> false;
		                predicate Q_() = [1/2]lock.clientOwner |-> clientOwner &*& [1/2]lock.clientHeld |-> true;
		                produce_lemma_function_pointer_chunk CohortLock_acquire_op(lock, clientOwner, P_, Q_)() {
		                    open P_();
		                    open lock.state(_, _);
		                    lock.clientHeld = true;
		                    close lock.state(_, _);
		                    close Q_();
		                } {
		                    close P_();
		                    assert is_CohortLock_acquire_op(?op_, _, _, _, _);
    		                aop(clientOwner, op_);
    		                open Q_();
    		            }
		            }
		            leak is_CohortLock_acquire_ghost_op(_, _, _, _, _, _, _, _);
		            
		            handle globalOwnerHandle = create_has_at<int>(globalOwnersId, cohortOwner);
		            assert has_at<int>(globalOwnerHandle, globalOwnersId, cohortOwner, ?globalOwner);
		            handle globalRoundInfoId = create_has_at<global_round_info>(roundsInfoId, globalOwner);
		            close client_owner_info(globalOwnerHandle, globalRoundInfoId);
		            
		            close CohortLock_inv(lock)();
		            close_atomic_space(COHORTLOCK_NS, CohortLock_inv(lock));
		        } else {
		            op();
		            cohort.held_ = true;
		            
		            init_signal(acquireSignal, sublevel(level, SIG_LEVEL));
		        }
		        
		        create_has_at(acquireSignalsId, cohortOwner);
		        
		        close Cohort_inv(this)();
		        close_atomic_space(COHORT_NS, Cohort_inv(this));
		        
		        close post_(cohortOwner);
		    };
		    @*/
		    //@ is_ancestor_of_refl(p);
		    //@ close wait_inv_core(-1, -1);
		    //@ close wait_inv_(-1);
		    /*@
		    if (!forall(map(snd, obs), (level_subspace_lt)(LL_LEVEL))) {
		        level badLevel = not_forall(map(snd, obs), (level_subspace_lt)(LL_LEVEL));
		        forall_elim(map(snd, obs), (level_subspace_lt)(level), badLevel);
		        level_subspace_lt_sublevel(level, Cohort.LEVEL, badLevel);
		        assert false;
		    }
		    @*/
		    //@ produce_call_below_perm_();
		    //@ call_below_perm__weaken(Ticketlock.class);
		    ticketlock.acquire();
		    //@ open post_(?ticket);
		}
		//@ assert [1/8]cohort.owner |-> ?ticket;
		if (!cohort.passing) {
		    //@ assert obs(currentThread, p, cons(pair(?acquireSignal, sublevel(level, SIG_LEVEL)), obs));
		    {
				/*@
				predicate global_round_handle(handle globalRoundHandle, handle passCountHandle) = true;
				predicate wait_inv_(int oldGlobalOwner) =
				    [1/4]cohort._passing |-> false &*&
				    [1/4]cohort._passCount |-> ?passCount &*& cohort.passCount |-> passCount &*&
				    [1/8]cohort.held_ |-> true &*&
				    [1/8]cohort.owner |-> ticket &*&
				    [1/2]cohort.releasing |-> false &*&
				    has_at(_, acquireSignalsId, ticket, acquireSignal) &*&
				    [_]this.lock |-> lock &*&
				    [_]this.ticketlock |-> ticketlock &*& [_]ticketlock.valid(COHORT_TICKETLOCK_NS, LL_LEVEL) &*&
				    [_]lock.ns |-> ns &*&
				    [_]lock.level |-> level &*&
				    [_]lock.ticketlock |-> globalLock &*&
				    [_]lock.notAloneListId |-> notAloneListId &*&
				    [_]lock.roundsInfoId |-> roundsInfoId &*&
				    [_]lock.clientRoundsInfoId |-> clientRoundsInfoId &*&
				    [_]this.acquireSignalsId |-> acquireSignalsId &*&
				    [_]this.globalOwnersId |-> globalOwnersId &*&
				    [_]this.releaseSignalsId |-> releaseSignalsId &*&
				    [_]atomic_space_(append(ns, {CohortLock.NS_}), CohortLock_inv(lock)) &*&
				    [_]atomic_space_(append(ns, {NS_}), Cohort_inv(this)) &*&
				    is_CohortLock_wait_ghost_op(wop, p, lock, ns, level, cpDegrees, wait_inv, currentThread) &*&
				    is_CohortLock_acquire_ghost_op(aop, p, obs, lock, ns, wait_inv, post, currentThread) &*&
				    wait_inv(?oldClientOwner) &*&
				    oldGlobalOwner == -1 ?
				        true
				    :
				        global_round_handle(?globalRoundHandle, ?passCountHandle) &*&
				        has_at(globalRoundHandle, roundsInfoId, oldGlobalOwner, global_round_info(?oldOwnerCohort, ?oldPassCountIncrBox, ?oldInitialClientOwner, ?oldInitialLocalOwner)) &*&
				        is_lower_bound(passCountHandle, oldPassCountIncrBox, ?oldPassCount) &*& oldPassCount <= MAX_PASS_COUNT &*&
				        oldClientOwner == oldInitialClientOwner + oldPassCount &*&
				        call_below_perms_lex(MAX_PASS_COUNT - oldPassCount, p, ?c1, {cpDegrees}) &*& Class_lt(Ticketlock_targetClass, c1) == true;
				predicate post_(int globalTicket) =
				    [1/4]cohort._passing |-> true &*&
				    [1/4]cohort._passCount |-> 0 &*& cohort.passCount |-> 0 &*&
				    [1/8]cohort.held_ |-> true &*&
				    [1/8]cohort.owner |-> ticket &*&
				    [1/2]cohort.releasing |-> false &*&
				    [1/2]lock.notAloneLocally |-> _ &*&
		            post(?clientOwner) &*&
		            client_owner_info(?globalOwnerHandle, ?globalRoundInfoHandle) &*&
		            has_at<int>(globalOwnerHandle, globalOwnersId, ticket, globalTicket) &*&
		            has_at(globalRoundInfoHandle, roundsInfoId, globalTicket, global_round_info(cohort, ?passCountIncrBoxId, clientOwner, ticket));
				@*/
				/*@
				produce_lemma_function_pointer_chunk Ticketlock_wait_ghost_op(p, globalLock, append(ns, {CohortLock.TICKETLOCK_NS_}), sublevel(level, CohortLock.LEVEL), cpDegrees + 1, wait_inv_, currentThread)(globalOwner, newRound, op) {
				    open wait_inv_(?oldGlobalOwner);
				    assert obs(?callerThread, p, ?obs1);
				    
				    if (!forall(map(snd, obs1), (level_lt)(level))) {
				        level badLevel = not_forall(map(snd, obs1), (level_lt)(level));
				        forall_elim(map(snd, obs1), (level_lt)(TL_LEVEL), badLevel);
				        level_lt_append(level, {}, TL_LEVEL_);
				        level_lt_trans(level, TL_LEVEL, badLevel);
				        assert false;
				    }
				    
				    assert atomic_spaces(?spaces);
				    if (mem(pair(COHORTLOCK_NS, CohortLock_inv(lock)), spaces)) {
				        mem_map(pair(COHORTLOCK_NS, CohortLock_inv(lock)), spaces, fst);
				        forall_elim(map(fst, spaces), (is_prefix_of)(append(ns, {CohortLock.TICKETLOCK_NS_})), COHORTLOCK_NS);
				        assert false;
				    }
				    open_atomic_space(COHORTLOCK_NS, CohortLock_inv(lock));
				    open CohortLock_inv(lock)();
				    
				    is_prefix_of_append(ns, {}, {CohortLock.NS_});

				    if (!forall(map(fst, spaces), (is_prefix_of)(ns))) {
				        list<int> badName = not_forall(map(fst, spaces), (is_prefix_of)(ns));
				        forall_elim(map(fst, spaces), (is_prefix_of)(append(ns, {CohortLock.TICKETLOCK_NS_})), badName);
				        append_drop_take(badName, length(append(ns, {CohortLock.TICKETLOCK_NS_})));
				        assert badName == append(append(ns, {CohortLock.TICKETLOCK_NS_}), drop(length(ns) + 1, badName));
				        append_assoc(ns, {CohortLock.TICKETLOCK_NS_}, drop(length(ns) + 1, badName));
				        assert false;
				    }
				    				    
				    op();
				    
				    if (newRound) {
				        if (oldGlobalOwner != -1) {
				            open global_round_handle(?oldGlobalRoundHandle, ?oldPassCountHandle);
				            leak has_at(oldGlobalRoundHandle, _, _, _);
				            leak is_lower_bound(oldPassCountHandle, _, _);
				            leak call_below_perms_lex(_, _, _, _);
				        }
				        
				        handle globalRoundHandle = create_has_at<global_round_info>(roundsInfoId, globalOwner);
				        assert has_at(globalRoundHandle, roundsInfoId, globalOwner, global_round_info(?ownerCohort, ?passCountIncrBox, _, _));
				        consuming_box_predicate incr_box(passCountIncrBox, ?passCount)
				        perform_action noop() {}
				        producing_fresh_handle_predicate is_lower_bound(passCount);
				        assert is_lower_bound(?passCountHandle, passCountIncrBox, passCount);
				        close global_round_handle(globalRoundHandle, passCountHandle);
				        open cp_lex(p, Ticketlock_targetClass, {cpDegrees + 1});
				        call_below_perm_lex_weaken_multi(0, MAX_PASS_COUNT - passCount + 1, {cpDegrees});
				        open call_below_perms(0, _, _);
				        open call_below_perms_lex(_, _, _, _);
				        close cp_lex(p, CohortLock_targetClass, {cpDegrees});
				    }
			        open global_round_handle(?globalRoundHandle, ?passCountHandle);
			        assert has_at(globalRoundHandle, roundsInfoId, globalOwner, global_round_info(?ownerCohort, ?passCountIncrBox, ?initialClientOwner, ?initialLocalOwner));
			        match_has_at_(globalRoundHandle);
			        consuming_box_predicate incr_box(passCountIncrBox, ?passCount)
			        consuming_handle_predicate is_lower_bound(passCountHandle, ?oldPassCount)
			        perform_action noop() {}
			        producing_fresh_handle_predicate is_lower_bound(passCount);
			        assert is_lower_bound(?newPassCountHandle, passCountIncrBox, passCount);
			        close global_round_handle(globalRoundHandle, newPassCountHandle);
				        
			        if (oldPassCount != passCount) {
			            call_below_perms_lex_weaken(MAX_PASS_COUNT - passCount + 1);
			            open call_below_perms_lex(_, _, _, _);
			            close cp_lex(p, CohortLock_targetClass, {cpDegrees});
			        }
				        
			        if (!ownerCohort.held_) {
			            is_prefix_of_append(ns, {Cohort.TICKETLOCK_NS_}, {CohortLock.NS_});
			            assert not_is_prefix_of(append(ns, {Cohort.TICKETLOCK_NS_}), append(ns, {CohortLock.NS_})) == true;
			            if (!forall(map(fst, spaces), (not_is_prefix_of)(append(ns, {Cohort.TICKETLOCK_NS_})))) {
			                list<int> badNs = not_forall(map(fst, spaces), (not_is_prefix_of)(append(ns, {Cohort.TICKETLOCK_NS_})));
			                forall_elim(map(fst, spaces), (is_prefix_of)(append(ns, {CohortLock.TICKETLOCK_NS_})), badNs);
			                drop_append(ns, {Cohort.TICKETLOCK_NS_});
			                assert false;
			            }
			            Ticketlock_not_alone_elim(ownerCohort.ticketlock);
			            assert false;
			        }
			        
			        {
			            predicate P_() = [1/2]lock.clientOwner |-> initialClientOwner + passCount &*& [1/2]lock.clientHeld |-> true;
			            produce_lemma_function_pointer_chunk CohortLock_wait_op(lock, initialClientOwner + passCount, P_)() {
			                open P_();
			                open lock.state(_, _);
			                close lock.state(_, _);
			                close P_();
			            } {
			                close P_();
			                assert is_CohortLock_wait_op(?op_, _, _, _);
			                wop(initialClientOwner + passCount, newRound || oldPassCount != passCount, op_);
			                open P_();
			            }
			        }
				    
				    close CohortLock_inv(lock)();
				    close_atomic_space(COHORTLOCK_NS, CohortLock_inv(lock));
				    close wait_inv_(globalOwner);
				};
				@*/
				/*@
				produce_lemma_function_pointer_chunk Ticketlock_acquire_ghost_op(p, cons(pair(acquireSignal, sublevel(level, SIG_LEVEL)), obs), globalLock, append(ns, {CohortLock.TICKETLOCK_NS_}), wait_inv_, post_, currentThread)(globalOwner, op) {
				    open wait_inv_(?oldGlobalOwner);
				    assert atomic_spaces(?spaces);
				    if (mem(pair(COHORTLOCK_NS, CohortLock_inv(lock)), spaces)) {
				        mem_map(pair(COHORTLOCK_NS, CohortLock_inv(lock)), spaces, fst);
				        forall_elim(map(fst, spaces), (is_prefix_of)(append(ns, {CohortLock.TICKETLOCK_NS_})), COHORTLOCK_NS);
				        assert false;
				    }
				    open_atomic_space(COHORTLOCK_NS, CohortLock_inv(lock));
				    open CohortLock_inv(lock)();
				    
				    is_prefix_of_append(ns, {}, {CohortLock.NS_});

				    if (!forall(map(fst, spaces), (is_prefix_of)(ns))) {
				        list<int> badName = not_forall(map(fst, spaces), (is_prefix_of)(ns));
				        forall_elim(map(fst, spaces), (is_prefix_of)(append(ns, {CohortLock.TICKETLOCK_NS_})), badName);
				        append_drop_take(badName, length(append(ns, {CohortLock.TICKETLOCK_NS_})));
				        assert badName == append(append(ns, {CohortLock.TICKETLOCK_NS_}), drop(length(ns) + 1, badName));
				        append_assoc(ns, {CohortLock.TICKETLOCK_NS_}, drop(length(ns) + 1, badName));
				        assert false;
				    }
				    				    
				    op();
				    
				    is_prefix_of_append(ns, {CohortLock.NS_}, {Cohort.NS_});
				    if (mem(pair(COHORT_NS, Cohort_inv(this)), spaces)) {
				        mem_map(pair(COHORT_NS, Cohort_inv(this)), spaces, fst);
				        forall_elim(map(fst, spaces), (is_prefix_of)(append(ns, {CohortLock.TICKETLOCK_NS_})), COHORT_NS);
				        assert false;
				    }
				    open_atomic_space(COHORT_NS, Cohort_inv(this));
				    open Cohort_inv(this)();
				    
				    match_has_at(acquireSignalsId);
				    
				    set_signal(acquireSignal);
				    
				    lock.held_ = true;
				    
				    assert [_]lock.clientOwner |-> ?clientOwner;
				    
		            is_prefix_of_append(ns, {}, {CohortLock.NS_});
		            is_prefix_of_append(ns, {}, {COHORT_NS_});
		            {
		                predicate P_() = [1/2]lock.clientOwner |-> clientOwner &*& [1/2]lock.clientHeld |-> false;
		                predicate Q_() = [1/2]lock.clientOwner |-> clientOwner &*& [1/2]lock.clientHeld |-> true;
		                produce_lemma_function_pointer_chunk CohortLock_acquire_op(lock, clientOwner, P_, Q_)() {
		                    open P_();
		                    open lock.state(_, _);
		                    lock.clientHeld = true;
		                    close lock.state(_, _);
		                    close Q_();
		                } {
		                    close P_();
		                    assert is_CohortLock_acquire_op(?op_, _, _, _, _);
    		                aop(clientOwner, op_);
    		                open Q_();
    		            }
		            }
		            leak is_CohortLock_acquire_ghost_op(_, _, _, _, _, _, _, _);
		            
		            assert growing_list<int>(globalOwnersId, ?globalOwners);
		            growing_list_add(globalOwnersId, globalOwner);
		            
		            create_box passCountIncrBoxId = incr_box(0); 
		            
		            growing_list_add(roundsInfoId, global_round_info(this, passCountIncrBoxId, clientOwner, ticket));
		            handle globalRoundInfoId = create_has_at<global_round_info>(roundsInfoId, globalOwner);
		            handle globalOwnerHandle = create_has_at<int>(globalOwnersId, ticket);
		            close client_owner_info(globalOwnerHandle, globalRoundInfoId);
		            
		            handle passingGlobalOwnerHandle = create_has_at<global_round_info>(roundsInfoId, globalOwner);
		            close passing_global_owner_handle(passingGlobalOwnerHandle);
		            
		            _passing = true;
		            
		            assert growing_list<client_round_info>(clientRoundsInfoId, ?clientRoundsInfo);
		            growing_list_add(clientRoundsInfoId, client_round_info(this, ticket));
		            
		            close Cohort_inv(this)();
		            close_atomic_space(COHORT_NS, Cohort_inv(this));
				    
				    close CohortLock_inv(lock)();
				    close_atomic_space(COHORTLOCK_NS, CohortLock_inv(lock));
				    close post_(globalOwner);
				};
				@*/
				//@ assert level == level(_, cons(?maxLength, ?level0));
				//@ lex0_subspace_lt_append(level0, CohortLock.LEVEL, SIG_LEVEL);
				/*@
				if (!forall(map(snd, obs), (level_subspace_lt)(TL_LEVEL))) {
				    level badLevel = not_forall(map(snd, obs), (level_subspace_lt)(TL_LEVEL));
				    forall_elim(map(snd, obs), (level_subspace_lt)(level), badLevel);
				    level_subspace_lt_sublevel(level, CohortLock.LEVEL, badLevel);
				    assert false;
				}
				@*/
				//@ produce_call_below_perm_();
				//@ call_below_perm__weaken(Ticketlock.class);
				//@ close wait_inv_(-1);
				globalLock.acquire();
				//@ open post_(?globalTicket);
			}
		}
		//@ close Cohort_held(cohort, _);
	}

	boolean alone()
	//@ requires [_]valid(?lock_) &*& [_]lock_.valid(?ns, ?level) &*& Cohort_held(this, ?owner) &*& is_CohortLock_alone_ghost_op(?ghop, lock_, ns, owner, ?pre, ?post) &*& pre();
	//@ ensures Cohort_held(this, owner) &*& result ? post() : pre() &*& CohortLock_not_alone(lock_, owner);
	//@ terminates;
	{
	    //@ open valid(lock_);
	    CohortLock lock = this.lock;
	    //@ open lock.valid(ns, level);
	    Ticketlock ticketlock = this.ticketlock;
	    Ticketlock globalLock = lock.ticketlock;
	    //@ open Cohort_held(this, owner);
	    int passCount = this.passCount;
	    //@ assert ticketlock.held(?cohortTicket);
	    //@ assert globalLock.held(?globalTicket);
	    //@ assert client_owner_info(?globalOwnerHandle, ?globalRoundInfoHandle);
	    //@ box notAloneListId = lock.notAloneListId;
	    //@ box roundsInfoId = lock.roundsInfoId;
	    //@ box globalOwnersId = this.globalOwnersId;
		//@ assert has_at(globalRoundInfoHandle, roundsInfoId, globalTicket, global_round_info(this, ?passCountIncrBoxId, ?initialClientOwner, ?initialLocalOwner));
		boolean globalAlone;
		{
		    /*@
		    predicate pre_() =
		        [_]this.lock |-> lock &*&
		        [_]this.globalOwnersId |-> globalOwnersId &*&
		        [_]lock.ticketlock |-> globalLock &*&
		        [_]lock.roundsInfoId |-> roundsInfoId &*&
		        [_]lock.notAloneListId |-> notAloneListId &*&
		        [_]atomic_space_(append(ns, {Cohort.NS_}), Cohort_inv(this)) &*&
		        [_]atomic_space_(append(ns, {CohortLock.NS_}), CohortLock_inv(lock)) &*&
				[1/4]this._passing |-> true &*&
				[1/4]this._passCount |-> passCount &*&
				[1/8]this.held_ |-> true &*&
				[1/8]this.owner |-> cohortTicket &*&
				[1/2]this.releasing |-> false &*&
				has_at<int>(globalOwnerHandle, globalOwnersId, cohortTicket, globalTicket) &*&
		        has_at(globalRoundInfoHandle, roundsInfoId, globalTicket, global_round_info(this, passCountIncrBoxId, initialClientOwner, initialLocalOwner)) &*&
		        [1/2]lock.notAloneLocally |-> _;
		    predicate post_() =
				[1/4]this._passing |-> true &*&
				[1/4]this._passCount |-> passCount &*&
				[1/8]this.held_ |-> true &*&
				[1/8]this.owner |-> cohortTicket &*&
				[1/2]this.releasing |-> false &*&
				has_at<int>(globalOwnerHandle, globalOwnersId, cohortTicket, globalTicket) &*&
		        has_at(globalRoundInfoHandle, roundsInfoId, globalTicket, global_round_info(this, passCountIncrBoxId, initialClientOwner, initialLocalOwner)) &*&
		        [1/2]lock.notAloneLocally |-> true;
		    @*/
		    /*@
		    produce_lemma_function_pointer_chunk Ticketlock_alone_ghost_op(globalLock, append(ns, {CohortLock.TICKETLOCK_NS_}), globalTicket, pre_, post_)(op) {
			    open pre_();
			    assert atomic_spaces(?spaces);
			    if (mem(pair(append(ns, {Cohort.NS_}), Cohort_inv(this)), spaces)) {
			        mem_map(pair(append(ns, {Cohort.NS_}), Cohort_inv(this)), spaces, fst);
			        drop_append(ns, {CohortLock.TICKETLOCK_NS_});
			        drop_append(ns, {Cohort.NS_});
			        forall_elim(map(fst, spaces), (is_prefix_of)(append(ns, {CohortLock.TICKETLOCK_NS_})), append(ns, {Cohort.NS_}));
			        assert false;
			    }
			    if (mem(pair(append(ns, {CohortLock.NS_}), CohortLock_inv(lock)), spaces)) {
			        mem_map(pair(append(ns, {CohortLock.NS_}), CohortLock_inv(lock)), spaces, fst);
			        drop_append(ns, {CohortLock.TICKETLOCK_NS_});
			        drop_append(ns, {CohortLock.NS_});
			        forall_elim(map(fst, spaces), (is_prefix_of)(append(ns, {CohortLock.TICKETLOCK_NS_})), append(ns, {CohortLock.NS_}));
			        assert false;
			    }
			    drop_append(ns, {Cohort.NS_});
			    drop_append(ns, {CohortLock.TICKETLOCK_NS_});
			    open_atomic_space(append(ns, {Cohort.NS_}), Cohort_inv(this));
			    open Cohort_inv(this)();
			    
			    match_has_at_<int>(globalOwnerHandle);
			    assert passing_global_owner_handle(?passingGlobalOwnerHandle);
			    
		        open_atomic_space(append(ns, {CohortLock.NS_}), CohortLock_inv(lock));
		        open CohortLock_inv(lock)();
		        
		        match_has_at_(passingGlobalOwnerHandle);
		        merge_fractions this.owner |-> _;
		        merge_fractions this.held_ |-> _;
		        merge_fractions this.ticketlock |-> _;
		        
		        match_has_at_<global_round_info>(globalRoundInfoHandle);
		        assert [_]lock.held_ |-> true;
		        assert [_]lock.owner |-> globalTicket;
		        
		        if (!lock.notAloneLocally) {
		            assert growing_list<boolean>(notAloneListId, ?notAloneList);
		            if (length(notAloneList) > lock.clientOwner) {
		                op();
		                assert false;
		            }
		            lock.notAloneLocally = true;
		        }
		        
		        close Cohort_inv(this)();
		        close_atomic_space(append(ns, {Cohort.NS_}), Cohort_inv(this));
		        
		        close CohortLock_inv(lock)();
		        close_atomic_space(append(ns, {CohortLock.NS_}), CohortLock_inv(lock));
		        close post_();
		    };
		    @*/
		    //@ close pre_();
		    globalAlone = globalLock.alone();
		    //@ if (globalAlone) open post_(); else open pre_();
		}
	    if (!globalAlone) {
	        /*@
	        predicate pre_() =
	            [_]this.lock |-> lock &*& [_]lock.valid(ns, level) &*&
	            [_]this.ticketlock |-> ticketlock &*&
	            [_]this.globalOwnersId |-> globalOwnersId &*&
	            [_]lock.ticketlock |-> globalLock &*&
	            [_]lock.notAloneListId |-> notAloneListId &*&
	            [_]lock.roundsInfoId |-> roundsInfoId &*&
	            [_]atomic_space_(append(ns, {Cohort.NS_}), Cohort_inv(this)) &*&
	            [_]atomic_space_(append(ns, {CohortLock.NS_}), CohortLock_inv(lock)) &*&
	            [1/4]this._passing |-> true &*&
	            [1/4]this._passCount |-> passCount &*&
	            [1/8]this.held_ |-> true &*&
	            [1/8]this.owner |-> cohortTicket &*&
	            [1/2]this.releasing |-> false &*&
				has_at<int>(globalOwnerHandle, globalOwnersId, cohortTicket, globalTicket) &*&
				has_at(globalRoundInfoHandle, roundsInfoId, globalTicket, global_round_info(this, passCountIncrBoxId, initialClientOwner, initialLocalOwner)) &*&
				[1/2]lock.notAloneLocally |-> _ &*&
	            Ticketlock_not_alone(globalLock, globalTicket);
	        predicate post_() =
	            [1/4]this._passing |-> true &*&
	            [1/4]this._passCount |-> passCount &*&
	            [1/8]this.held_ |-> true &*&
	            [1/8]this.owner |-> cohortTicket &*&
	            [1/2]this.releasing |-> false &*&
				has_at<int>(globalOwnerHandle, globalOwnersId, cohortTicket, globalTicket) &*&
				has_at(globalRoundInfoHandle, roundsInfoId, globalTicket, global_round_info(this, passCountIncrBoxId, initialClientOwner, initialLocalOwner)) &*&
				[1/2]lock.notAloneLocally |-> _ &*&
	            CohortLock_not_alone(lock, owner);
	        @*/
	        /*@
	        produce_lemma_function_pointer_chunk atomic_noop_ghost_op(pre_, post_)() {
	            open pre_();
	            open_atomic_space(append(ns, {Cohort.NS_}), Cohort_inv(this));
	            open Cohort_inv(this)();
	            
	            match_has_at_<int>(globalOwnerHandle);
	            
	            drop_append(ns, {Cohort.NS_});
	            drop_append(ns, {CohortLock.NS_});
	            open_atomic_space(append(ns, {CohortLock.NS_}), CohortLock_inv(lock));
	            open CohortLock_inv(lock)();
	            
	            match_has_at_(globalRoundInfoHandle);
	            merge_fractions this.owner |-> _;
	            merge_fractions this.held_ |-> _;
	            merge_fractions this.ticketlock |-> _;
	            merge_fractions this._passCount |-> _;
	            
	            assert growing_list<boolean>(notAloneListId, ?notAloneList);
	            if (length(notAloneList) == lock.clientOwner) {
	                growing_list_add<boolean>(notAloneListId, true);
	                lock.notAloneLocally = false;
	            }
	            handle notAloneHandle = create_has_at<boolean>(notAloneListId, lock.clientOwner);
	            close exists(notAloneHandle);
	            close CohortLock_not_alone(lock, owner);
	            
	            close CohortLock_inv(lock)();
	            close_atomic_space(append(ns, {CohortLock.NS_}), CohortLock_inv(lock));
	            
	            close Cohort_inv(this)();
	            close_atomic_space(append(ns, {Cohort.NS_}), Cohort_inv(this));
	            close post_();
	        };
	        @*/
	        //@ close pre_();
	        //@ atomic_noop();
	        //@ open post_();
	        //@ close Cohort_held(this, owner);
	        return false;
	    }
	    boolean localAlone;
	    {
		    /*@
		    predicate pre_() =
    		    is_CohortLock_alone_ghost_op(ghop, lock_, ns, owner, pre, post) &*& pre() &*&
		        [_]this.lock |-> lock &*&
		        [_]this.globalOwnersId |-> globalOwnersId &*&
		        [_]this.ticketlock |-> ticketlock &*&
		        [_]lock.ticketlock |-> globalLock &*&
		        [_]lock.roundsInfoId |-> roundsInfoId &*&
		        [_]lock.notAloneListId |-> notAloneListId &*&
		        [_]atomic_space_(append(ns, {Cohort.NS_}), Cohort_inv(this)) &*&
		        [_]atomic_space_(append(ns, {CohortLock.NS_}), CohortLock_inv(lock)) &*&
				[1/4]this._passing |-> true &*&
				[1/4]this._passCount |-> passCount &*&
				[1/8]this.held_ |-> true &*&
				[1/8]this.owner |-> cohortTicket &*&
				[1/2]this.releasing |-> false &*&
				has_at<int>(globalOwnerHandle, globalOwnersId, cohortTicket, globalTicket) &*&
		        has_at(globalRoundInfoHandle, roundsInfoId, globalTicket, global_round_info(this, passCountIncrBoxId, initialClientOwner, initialLocalOwner)) &*&
		        [1/2]lock.notAloneLocally |-> true;
		    predicate post_() =
		        post() &*&
				[1/4]this._passing |-> true &*&
				[1/4]this._passCount |-> passCount &*&
				[1/8]this.held_ |-> true &*&
				[1/8]this.owner |-> cohortTicket &*&
				[1/2]this.releasing |-> false &*&
				has_at<int>(globalOwnerHandle, globalOwnersId, cohortTicket, globalTicket) &*&
		        has_at(globalRoundInfoHandle, roundsInfoId, globalTicket, global_round_info(this, passCountIncrBoxId, initialClientOwner, initialLocalOwner)) &*&
		        [1/2]lock.notAloneLocally |-> _;
		    @*/
		    /*@
		    produce_lemma_function_pointer_chunk Ticketlock_alone_ghost_op(ticketlock, append(ns, {Cohort.TICKETLOCK_NS_}), cohortTicket, pre_, post_)(op) {
			    open pre_();
			    assert atomic_spaces(?spaces);
			    if (mem(pair(append(ns, {Cohort.NS_}), Cohort_inv(this)), spaces)) {
			        mem_map(pair(append(ns, {Cohort.NS_}), Cohort_inv(this)), spaces, fst);
			        drop_append(ns, {CohortLock.TICKETLOCK_NS_});
			        drop_append(ns, {Cohort.NS_});
			        forall_elim(map(fst, spaces), (is_prefix_of)(append(ns, {Cohort.TICKETLOCK_NS_})), append(ns, {Cohort.NS_}));
			        assert false;
			    }
			    if (mem(pair(append(ns, {CohortLock.NS_}), CohortLock_inv(lock)), spaces)) {
			        mem_map(pair(append(ns, {CohortLock.NS_}), CohortLock_inv(lock)), spaces, fst);
			        drop_append(ns, {CohortLock.TICKETLOCK_NS_});
			        drop_append(ns, {CohortLock.NS_});
			        forall_elim(map(fst, spaces), (is_prefix_of)(append(ns, {Cohort.TICKETLOCK_NS_})), append(ns, {CohortLock.NS_}));
			        assert false;
			    }
			    drop_append(ns, {Cohort.NS_});
			    drop_append(ns, {CohortLock.TICKETLOCK_NS_});
			    open_atomic_space(append(ns, {Cohort.NS_}), Cohort_inv(this));
			    open Cohort_inv(this)();
			    
			    match_has_at_<int>(globalOwnerHandle);
			    assert passing_global_owner_handle(?passingGlobalOwnerHandle);
			    
		        open_atomic_space(append(ns, {CohortLock.NS_}), CohortLock_inv(lock));
		        open CohortLock_inv(lock)();
		        
		        match_has_at_(passingGlobalOwnerHandle);
		        merge_fractions this.owner |-> _;
		        merge_fractions this.held_ |-> _;
		        merge_fractions this.ticketlock |-> _;
		        
		        match_has_at_<global_round_info>(globalRoundInfoHandle);
		        assert [_]lock.held_ |-> true;
		        assert [_]lock.owner |-> globalTicket;
		        
	            assert growing_list<boolean>(notAloneListId, ?notAloneList);
	            if (length(notAloneList) > lock.clientOwner) {
	                op();
	                assert false;
	            }
	            {
	                predicate P_() = [_]lock.notAloneListId |-> notAloneListId &*& growing_list(notAloneListId, notAloneList);
	                produce_lemma_function_pointer_chunk CohortLock_alone_op(lock, owner, P_)() {
	                    open P_();
	                    open CohortLock_not_alone(lock, owner);
	                    match_has_at(notAloneListId);
	                    assert false;
	                } {
	                    close P_();
	                    assert is_CohortLock_alone_op(?op_, _, _, _);
	                    is_prefix_of_append(ns, {}, {Cohort.NS_});
	                    is_prefix_of_append(ns, {}, {CohortLock.NS_});
						if (!forall(map(fst, spaces), (is_prefix_of)(ns))) {
							list<int> badName = not_forall(map(fst, spaces), (is_prefix_of)(ns));
							forall_elim(map(fst, spaces), (is_prefix_of)(append(ns, {Cohort.TICKETLOCK_NS_})), badName);
							length_take_(length(ns) + 1, badName);
							append_drop_take(badName, length(append(ns, {CohortLock.TICKETLOCK_NS_})));
							assert badName == append(append(ns, {Cohort.TICKETLOCK_NS_}), drop(length(ns) + 1, badName));
							append_assoc(ns, {Cohort.TICKETLOCK_NS_}, drop(length(ns) + 1, badName));
							assert false;
						}
	                    ghop(op_);
	                    open P_();
	                }
	            }
		        
		        close Cohort_inv(this)();
		        close_atomic_space(append(ns, {Cohort.NS_}), Cohort_inv(this));
		        
		        close CohortLock_inv(lock)();
		        close_atomic_space(append(ns, {CohortLock.NS_}), CohortLock_inv(lock));
		        close post_();
		    };
		    @*/
		    //@ close pre_();
	        localAlone = ticketlock.alone();
		    //@ if (localAlone) open post_(); else open pre_();
	    }
	    if (localAlone) {
	        //@ close Cohort_held(this, owner);
	        return true;
	    }
	    if (passCount == MAX_PASS_COUNT) {
		    /*@
		    predicate pre_() =
    		    is_CohortLock_alone_ghost_op(ghop, lock_, ns, owner, pre, post) &*& pre() &*&
		        [_]this.lock |-> lock &*&
		        [_]this.globalOwnersId |-> globalOwnersId &*&
		        [_]this.ticketlock |-> ticketlock &*&
		        [_]lock.ticketlock |-> globalLock &*&
		        [_]lock.roundsInfoId |-> roundsInfoId &*&
		        [_]lock.notAloneListId |-> notAloneListId &*&
		        [_]atomic_space_(append(ns, {Cohort.NS_}), Cohort_inv(this)) &*&
		        [_]atomic_space_(append(ns, {CohortLock.NS_}), CohortLock_inv(lock)) &*&
				[1/4]this._passing |-> true &*&
				[1/4]this._passCount |-> passCount &*&
				[1/8]this.held_ |-> true &*&
				[1/8]this.owner |-> cohortTicket &*&
				[1/2]this.releasing |-> false &*&
				has_at<int>(globalOwnerHandle, globalOwnersId, cohortTicket, globalTicket) &*&
		        has_at(globalRoundInfoHandle, roundsInfoId, globalTicket, global_round_info(this, passCountIncrBoxId, initialClientOwner, initialLocalOwner)) &*&
		        [1/2]lock.notAloneLocally |-> true;
		    predicate post_() =
		        post() &*&
				[1/4]this._passing |-> true &*&
				[1/4]this._passCount |-> passCount &*&
				[1/8]this.held_ |-> true &*&
				[1/8]this.owner |-> cohortTicket &*&
				[1/2]this.releasing |-> false &*&
				has_at<int>(globalOwnerHandle, globalOwnersId, cohortTicket, globalTicket) &*&
		        has_at(globalRoundInfoHandle, roundsInfoId, globalTicket, global_round_info(this, passCountIncrBoxId, initialClientOwner, initialLocalOwner)) &*&
		        [1/2]lock.notAloneLocally |-> _;
		    @*/
		    /*@
		    produce_lemma_function_pointer_chunk atomic_noop_ghost_op(pre_, post_)() {
			    open pre_();
			    drop_append(ns, {Cohort.NS_});
			    drop_append(ns, {CohortLock.TICKETLOCK_NS_});
			    open_atomic_space(append(ns, {Cohort.NS_}), Cohort_inv(this));
			    open Cohort_inv(this)();
			    
			    match_has_at_<int>(globalOwnerHandle);
			    assert passing_global_owner_handle(?passingGlobalOwnerHandle);
			    
		        open_atomic_space(append(ns, {CohortLock.NS_}), CohortLock_inv(lock));
		        open CohortLock_inv(lock)();
		        
		        match_has_at_(passingGlobalOwnerHandle);
		        merge_fractions this.owner |-> _;
		        merge_fractions this.held_ |-> _;
		        merge_fractions this.ticketlock |-> _;
		        
		        match_has_at_<global_round_info>(globalRoundInfoHandle);
		        assert [_]lock.held_ |-> true;
		        assert [_]lock.owner |-> globalTicket;
		        
	            assert growing_list<boolean>(notAloneListId, ?notAloneList);
	            assert length(notAloneList) == lock.clientOwner;
	            
	            {
	                predicate P_() = [_]lock.notAloneListId |-> notAloneListId &*& growing_list(notAloneListId, notAloneList);
	                produce_lemma_function_pointer_chunk CohortLock_alone_op(lock, owner, P_)() {
	                    open P_();
	                    open CohortLock_not_alone(lock, owner);
	                    match_has_at(notAloneListId);
	                    assert false;
	                } {
	                    close P_();
	                    assert is_CohortLock_alone_op(?op_, _, _, _);
	                    is_prefix_of_append(ns, {}, {Cohort.NS_});
	                    is_prefix_of_append(ns, {}, {CohortLock.NS_});
	                    ghop(op_);
	                    open P_();
	                }
	            }
		        
		        close Cohort_inv(this)();
		        close_atomic_space(append(ns, {Cohort.NS_}), Cohort_inv(this));
		        
		        close CohortLock_inv(lock)();
		        close_atomic_space(append(ns, {CohortLock.NS_}), CohortLock_inv(lock));
		        close post_();
		    };
		    @*/
		    //@ close pre_();
		    //@ atomic_noop();
		    //@ open post_();
	        //@ close Cohort_held(this, owner);
	        return true;
	    }
	    {
	        /*@
	        predicate pre_() =
	            [_]this.lock |-> lock &*& [_]lock.valid(ns, level) &*&
	            [_]this.ticketlock |-> ticketlock &*&
	            [_]this.globalOwnersId |-> globalOwnersId &*&
	            [_]lock.ticketlock |-> globalLock &*&
	            [_]lock.notAloneListId |-> notAloneListId &*&
	            [_]lock.roundsInfoId |-> roundsInfoId &*&
	            [_]atomic_space_(append(ns, {Cohort.NS_}), Cohort_inv(this)) &*&
	            [_]atomic_space_(append(ns, {CohortLock.NS_}), CohortLock_inv(lock)) &*&
	            [1/4]this._passing |-> true &*&
	            [1/4]this._passCount |-> passCount &*&
	            [1/8]this.held_ |-> true &*&
	            [1/8]this.owner |-> cohortTicket &*&
	            [1/2]this.releasing |-> false &*&
				has_at<int>(globalOwnerHandle, globalOwnersId, cohortTicket, globalTicket) &*&
				has_at(globalRoundInfoHandle, roundsInfoId, globalTicket, global_round_info(this, passCountIncrBoxId, initialClientOwner, initialLocalOwner)) &*&
	            Ticketlock_not_alone(ticketlock, cohortTicket) &*&
	            [1/2]lock.notAloneLocally |-> _;
	        predicate post_() =
	            [1/4]this._passing |-> true &*&
	            [1/4]this._passCount |-> passCount &*&
	            [1/8]this.held_ |-> true &*&
	            [1/8]this.owner |-> cohortTicket &*&
	            [1/2]this.releasing |-> false &*&
				has_at<int>(globalOwnerHandle, globalOwnersId, cohortTicket, globalTicket) &*&
				has_at(globalRoundInfoHandle, roundsInfoId, globalTicket, global_round_info(this, passCountIncrBoxId, initialClientOwner, initialLocalOwner)) &*&
	            CohortLock_not_alone(lock, owner) &*&
	            [1/2]lock.notAloneLocally |-> _;
	        @*/
	        /*@
	        produce_lemma_function_pointer_chunk atomic_noop_ghost_op(pre_, post_)() {
	            open pre_();
	            open_atomic_space(append(ns, {Cohort.NS_}), Cohort_inv(this));
	            open Cohort_inv(this)();
	            
	            match_has_at_<int>(globalOwnerHandle);
	            
	            drop_append(ns, {Cohort.NS_});
	            drop_append(ns, {CohortLock.NS_});
	            open_atomic_space(append(ns, {CohortLock.NS_}), CohortLock_inv(lock));
	            open CohortLock_inv(lock)();
	            
	            match_has_at_(globalRoundInfoHandle);
	            merge_fractions this.owner |-> _;
	            merge_fractions this.held_ |-> _;
	            merge_fractions this.ticketlock |-> _;
	            merge_fractions this._passCount |-> _;
	            
	            assert growing_list<boolean>(notAloneListId, ?notAloneList);
	            if (length(notAloneList) == lock.clientOwner) {
	                growing_list_add<boolean>(notAloneListId, true);
	                lock.notAloneLocally = true;
	            }
	            handle notAloneHandle = create_has_at<boolean>(notAloneListId, lock.clientOwner);
	            close exists(notAloneHandle);
	            close CohortLock_not_alone(lock, owner);
	            
	            close CohortLock_inv(lock)();
	            close_atomic_space(append(ns, {CohortLock.NS_}), CohortLock_inv(lock));
	            
	            close Cohort_inv(this)();
	            close_atomic_space(append(ns, {Cohort.NS_}), Cohort_inv(this));
	            close post_();
	        };
	        @*/
	        //@ close pre_();
	        //@ atomic_noop();
	        //@ open post_();
	    }
        //@ close Cohort_held(this, owner);
		return false;
	}

	void release()
	/*@
	requires
	    [_]valid(?lock_) &*& [_]lock_.valid(?ns, ?level) &*&
	    Cohort_held(this, ?ticket) &*& is_CohortLock_release_ghost_op(?ghop, lock_, ns, level, ticket, ?pre, ?post, currentThread) &*& pre();
	@*/
	//@ ensures post(?p, ?obs) &*& obs(currentThread, p, obs);
	//@ terminates;
	{
	    //@ open valid(lock_);
	    CohortLock lock = this.lock;
	    //@ box globalOwnersId = this.globalOwnersId;
	    //@ box releaseSignalsId = this.releaseSignalsId;
	    //@ open lock.valid(ns, level);
	    //@ box notAloneListId = lock.notAloneListId;
	    //@ box roundsInfoId = lock.roundsInfoId;
	    //@ box clientRoundsInfoId = lock.clientRoundsInfoId;
	    Ticketlock ticketlock = this.ticketlock;
	    Ticketlock globalLock = lock.ticketlock;
	    //@ open Cohort_held(this, ticket);
	    int passCount = this.passCount;
	    //@ assert ticketlock.held(?cohortTicket);
	    //@ assert globalLock.held(?globalTicket);
	    //@ open client_owner_info(?globalOwnerHandle, ?globalRoundInfoHandle);
	    //@ assert has_at(globalRoundInfoHandle, roundsInfoId, globalTicket, global_round_info(this, ?passCountIncrBoxId, ?initialClientOwner, ?initialLocalOwner));
	    boolean localAlone;
	    {
		    /*@
		    predicate pre_() =
		        [_]this.lock |-> lock &*&
		        [_]this.globalOwnersId |-> globalOwnersId &*&
		        [_]this.ticketlock |-> ticketlock &*&
		        [_]lock.ticketlock |-> globalLock &*&
		        [_]lock.roundsInfoId |-> roundsInfoId &*&
		        [_]lock.notAloneListId |-> notAloneListId &*&
		        [_]atomic_space_(append(ns, {Cohort.NS_}), Cohort_inv(this)) &*&
		        [_]atomic_space_(append(ns, {CohortLock.NS_}), CohortLock_inv(lock)) &*&
				[1/4]this._passing |-> true &*&
				[1/4]this._passCount |-> passCount &*&
				[1/8]this.held_ |-> true &*&
				[1/8]this.owner |-> cohortTicket &*&
				[1/2]this.releasing |-> false &*&
				has_at<int>(globalOwnerHandle, globalOwnersId, cohortTicket, globalTicket) &*&
		        has_at(globalRoundInfoHandle, roundsInfoId, globalTicket, global_round_info(this, passCountIncrBoxId, initialClientOwner, initialLocalOwner)) &*&
		        [1/2]lock.notAloneLocally |-> _;
		    predicate post_() =
				[1/4]this._passing |-> true &*&
				[1/4]this._passCount |-> passCount &*&
				[1/8]this.held_ |-> true &*&
				[1/8]this.owner |-> cohortTicket &*&
				[1/2]this.releasing |-> false &*&
				has_at<int>(globalOwnerHandle, globalOwnersId, cohortTicket, globalTicket) &*&
		        has_at(globalRoundInfoHandle, roundsInfoId, globalTicket, global_round_info(this, passCountIncrBoxId, initialClientOwner, initialLocalOwner)) &*&
		        [1/2]lock.notAloneLocally |-> false;
		    @*/
		    /*@
		    produce_lemma_function_pointer_chunk Ticketlock_alone_ghost_op(ticketlock, append(ns, {Cohort.TICKETLOCK_NS_}), cohortTicket, pre_, post_)(op) {
			    open pre_();
			    assert atomic_spaces(?spaces);
			    if (mem(pair(append(ns, {Cohort.NS_}), Cohort_inv(this)), spaces)) {
			        mem_map(pair(append(ns, {Cohort.NS_}), Cohort_inv(this)), spaces, fst);
			        drop_append(ns, {CohortLock.TICKETLOCK_NS_});
			        drop_append(ns, {Cohort.NS_});
			        forall_elim(map(fst, spaces), (is_prefix_of)(append(ns, {Cohort.TICKETLOCK_NS_})), append(ns, {Cohort.NS_}));
			        assert false;
			    }
			    if (mem(pair(append(ns, {CohortLock.NS_}), CohortLock_inv(lock)), spaces)) {
			        mem_map(pair(append(ns, {CohortLock.NS_}), CohortLock_inv(lock)), spaces, fst);
			        drop_append(ns, {CohortLock.TICKETLOCK_NS_});
			        drop_append(ns, {CohortLock.NS_});
			        forall_elim(map(fst, spaces), (is_prefix_of)(append(ns, {Cohort.TICKETLOCK_NS_})), append(ns, {CohortLock.NS_}));
			        assert false;
			    }
			    drop_append(ns, {Cohort.NS_});
			    drop_append(ns, {CohortLock.TICKETLOCK_NS_});
			    open_atomic_space(append(ns, {Cohort.NS_}), Cohort_inv(this));
			    open Cohort_inv(this)();
			    
			    match_has_at_<int>(globalOwnerHandle);
			    assert passing_global_owner_handle(?passingGlobalOwnerHandle);
			    
		        open_atomic_space(append(ns, {CohortLock.NS_}), CohortLock_inv(lock));
		        open CohortLock_inv(lock)();
		        
		        match_has_at_(passingGlobalOwnerHandle);
		        merge_fractions this.owner |-> _;
		        merge_fractions this.held_ |-> _;
		        merge_fractions this.ticketlock |-> _;
		        
		        match_has_at_<global_round_info>(globalRoundInfoHandle);
		        assert [_]lock.held_ |-> true;
		        assert [_]lock.owner |-> globalTicket;
		        
	            assert growing_list<boolean>(notAloneListId, ?notAloneList);
	            if (lock.notAloneLocally && length(notAloneList) > lock.clientOwner) {
	                op();
	                assert false;
	            }
	            lock.notAloneLocally = false;
		        
		        close Cohort_inv(this)();
		        close_atomic_space(append(ns, {Cohort.NS_}), Cohort_inv(this));
		        
		        close CohortLock_inv(lock)();
		        close_atomic_space(append(ns, {CohortLock.NS_}), CohortLock_inv(lock));
		        close post_();
		    };
		    @*/
		    //@ close pre_();
	        localAlone = ticketlock.alone();
		    //@ if (localAlone) open post_(); else open pre_();
	    }
		if (passing = (!localAlone && passCount < MAX_PASS_COUNT)) {
		    this.passCount++;
			{
			    /*@
			    predicate pre_() =
		            is_CohortLock_release_ghost_op(ghop, lock, ns, level, ticket, pre, post, currentThread) &*& pre() &*&
		            [_]this.lock |-> lock &*&
		            [_]this.ticketlock |-> ticketlock &*&
		            [_]this.globalOwnersId |-> globalOwnersId &*&
		            [_]this.releaseSignalsId |-> releaseSignalsId &*&
		            [_]lock.ns |-> ns &*&
		            [_]lock.level |-> level &*&
		            [_]lock.ticketlock |-> globalLock &*&
		            [_]lock.notAloneListId |-> notAloneListId &*&
		            [_]lock.roundsInfoId |-> roundsInfoId &*&
		            [_]lock.clientRoundsInfoId |-> clientRoundsInfoId &*&
		            [_]atomic_space_(append(ns, {Cohort.NS_}), Cohort_inv(this)) &*&
		            [_]atomic_space_(append(ns, {CohortLock.NS_}), CohortLock_inv(lock)) &*&
					has_at<int>(globalOwnerHandle, globalOwnersId, cohortTicket, globalTicket) &*&
					has_at(globalRoundInfoHandle, roundsInfoId, globalTicket, global_round_info(this, passCountIncrBoxId, initialClientOwner, initialLocalOwner)) &*&
					[1/4]this._passing |-> true &*& this.passing |-> true &*&
					[1/4]this._passCount |-> passCount &*& this.passCount |-> passCount + 1 &*&
					[1/8]this.held_ |-> true &*&
					[1/8]this.owner |-> cohortTicket &*&
					[1/2]lock.notAloneLocally |-> _ &*&
					Ticketlock_not_alone(ticketlock, cohortTicket) &*&
					globalLock.held(globalTicket) &*&
					[1/2]this.releasing |-> false;
		        predicate post_(list<pathcomp> p, list<pair<void *, level> > obs) =
		            post(p, obs) &*&
		            forall(map(snd, obs), (level_subspace_lt)(level)) == true;
		        @*/
		        /*@
		        produce_lemma_function_pointer_chunk Ticketlock_release_ghost_op(ticketlock, append(ns, {Cohort.TICKETLOCK_NS_}), sublevel(level, LEVEL), cohortTicket, pre_, post_, currentThread)(op) {
		            open pre_();
		            assert atomic_spaces(?spaces);
				    if (mem(pair(append(ns, {CohortLock.NS_}), CohortLock_inv(lock)), spaces)) {
				        mem_map(pair(append(ns, {CohortLock.NS_}), CohortLock_inv(lock)), spaces, fst);
				        drop_append(ns, {CohortLock.TICKETLOCK_NS_});
				        drop_append(ns, {CohortLock.NS_});
				        forall_elim(map(fst, spaces), (is_prefix_of)(append(ns, {Cohort.TICKETLOCK_NS_})), append(ns, {CohortLock.NS_}));
				        assert false;
				    }
				    drop_append(ns, {NS_});
				    drop_append(ns, {CohortLock.NS_});
				    if (mem(pair(append(ns, {Cohort.NS_}), Cohort_inv(this)), spaces)) {
				        mem_map(pair(append(ns, {Cohort.NS_}), Cohort_inv(this)), spaces, fst);
				        forall_elim(map(fst, spaces), (is_prefix_of)(append(ns, {Cohort.TICKETLOCK_NS_})), append(ns, {Cohort.NS_}));
				        assert false;
				    }
		            open_atomic_space(append(ns, {Cohort.NS_}), Cohort_inv(this));
		            open Cohort_inv(this)();
		            match_has_at_<int>(globalOwnerHandle);
		            assert passing_global_owner_handle(?passingGlobalOwnerHandle);
		            
		            open_atomic_space(append(ns, {CohortLock.NS_}), CohortLock_inv(lock));
		            open CohortLock_inv(lock)();
		            match_has_at_(globalRoundInfoHandle);
		            match_has_at_(passingGlobalOwnerHandle);
		            merge_fractions this.owner |-> _;
		            merge_fractions this.held_ |-> _;
		            merge_fractions this._passing |-> _;
		            merge_fractions this._passCount |-> _;
		            merge_fractions this.ticketlock |-> _;
		            
		            int clientOwner = lock.clientOwner;
		            
		            {
		                predicate P_() = [1/2]lock.clientOwner |-> clientOwner &*& [1/2]lock.clientHeld |-> true;
		                predicate Q_() = [1/2]lock.clientOwner |-> clientOwner + 1 &*& [1/2]lock.clientHeld |-> false;
		                produce_lemma_function_pointer_chunk CohortLock_release_op(lock, clientOwner, P_, Q_)() {
		                    open P_();
		                    open lock.state(_, _);
		                    lock.clientOwner++;
		                    lock.clientHeld = false;
		                    close lock.state(_, _);
		                    close Q_();
		                } {
		                    close P_();
		                    assert is_CohortLock_release_op(?op_, _, _, _, _);
		                    is_prefix_of_append(ns, {}, {Cohort.NS_});
		                    is_prefix_of_append(ns, {}, {CohortLock.NS_});
							if (!forall(map(fst, spaces), (is_prefix_of)(ns))) {
								list<int> badName = not_forall(map(fst, spaces), (is_prefix_of)(ns));
								forall_elim(map(fst, spaces), (is_prefix_of)(append(ns, {Cohort.TICKETLOCK_NS_})), badName);
								length_take_(length(ns) + 1, badName);
								append_drop_take(badName, length(append(ns, {Cohort.TICKETLOCK_NS_})));
								assert badName == append(append(ns, {Cohort.TICKETLOCK_NS_}), drop(length(ns) + 1, badName));
								append_assoc(ns, {Cohort.TICKETLOCK_NS_}, drop(length(ns) + 1, badName));
								assert false;
							}
		                    ghop(op_);
		                    open Q_();
		                }
		            }
		            
		            op();
		            
		            this.owner++;
		            this.held_ = false;
		            this._passCount++;
		            
		            growing_list_add<int>(globalOwnersId, globalTicket);
		            void *releaseSignal = create_signal();
		            growing_list_add<void *>(releaseSignalsId, releaseSignal);
		            
		            assert growing_list<boolean>(notAloneListId, ?notAloneList);
		            if (length(notAloneList) == clientOwner) {
		                growing_list_add(notAloneListId, false);
		            }
		            
		            assert growing_list<client_round_info>(clientRoundsInfoId, ?clientRoundsInfo);
		            growing_list_add(clientRoundsInfoId, client_round_info(this, cohortTicket + 1));
		            nth_append_r(clientRoundsInfo, {client_round_info(this, cohortTicket + 1)}, 0);
		            
		            consuming_box_predicate incr_box(passCountIncrBoxId, passCount)
		            perform_action incr() {}
		            producing_box_predicate incr_box(passCount + 1);
		            
		            close CohortLock_inv(lock)();
		            close_atomic_space(append(ns, {CohortLock.NS_}), CohortLock_inv(lock));
		            
		            assert obs(_, ?p, ?clientObs);
		            
		            close Cohort_inv(this)();
		            close_atomic_space(append(ns, {Cohort.NS_}), Cohort_inv(this));
		            assert obs(_, _, ?obs);
		            close post_(p, obs);
		            
		            if (!forall(map(snd, clientObs), (level_subspace_lt)(sublevel(level, Cohort.LEVEL)))) {
		                level badLevel = not_forall(map(snd, clientObs), (level_subspace_lt)(sublevel(level, Cohort.LEVEL)));
		                forall_elim(map(snd, clientObs), (level_subspace_lt)(level), badLevel);
		                level_subspace_lt_sublevel(level, Cohort.LEVEL, badLevel);
		                assert false;
		            }
		        };
		        @*/
		        //@ close pre_();
				ticketlock.release();
		        //@ open post_(_, _);
			}
		} else {
		    this.passCount = 0;
		    {
		        /*@
		        predicate pre_() =
		            is_CohortLock_release_ghost_op(ghop, lock, ns, level, ticket, pre, post, currentThread) &*& pre() &*&
		            [_]this.lock |-> lock &*&
		            [_]this.globalOwnersId |-> globalOwnersId &*&
		            [_]this.releaseSignalsId |-> releaseSignalsId &*&
		            [_]lock.ns |-> ns &*&
		            [_]lock.level |-> level &*&
		            [_]lock.ticketlock |-> globalLock &*&
		            [_]lock.notAloneListId |-> notAloneListId &*&
		            [_]lock.roundsInfoId |-> roundsInfoId &*&
		            [_]atomic_space_(append(ns, {Cohort.NS_}), Cohort_inv(this)) &*&
		            [_]atomic_space_(append(ns, {CohortLock.NS_}), CohortLock_inv(lock)) &*&
					has_at<int>(globalOwnerHandle, globalOwnersId, cohortTicket, globalTicket) &*&
					has_at(globalRoundInfoHandle, roundsInfoId, globalTicket, global_round_info(this, passCountIncrBoxId, initialClientOwner, initialLocalOwner)) &*&
					[1/4]this._passing |-> true &*& this.passing |-> false &*&
					[1/4]this._passCount |-> passCount &*& this.passCount |-> 0 &*&
					[1/8]this.held_ |-> true &*&
					[1/8]this.owner |-> cohortTicket &*&
					[1/2]lock.notAloneLocally |-> ?notAloneLocally &*& !notAloneLocally || passCount >= MAX_PASS_COUNT &*&
					[1/2]this.releasing |-> false;
		        predicate post_(list<pathcomp> p, list<pair<void *, level> > obs) =
		            post(p, ?clientObs) &*&
		            forall(map(snd, clientObs), (level_subspace_lt)(level)) == true &*&
					[1/4]this._passing |-> false &*& this.passing |-> false &*&
					[1/4]this._passCount |-> 0 &*& this.passCount |-> 0 &*&
					[1/8]this.held_ |-> true &*&
					[1/8]this.owner |-> cohortTicket &*&
					[1/2]this.releasing |-> true &*&
					has_at<void *>(_, releaseSignalsId, cohortTicket, ?releaseSignal) &*&
		            obs == cons(pair(releaseSignal, sublevel(level, SIG_LEVEL)), clientObs);
		        @*/
		        /*@
		        produce_lemma_function_pointer_chunk Ticketlock_release_ghost_op(globalLock, append(ns, {CohortLock.TICKETLOCK_NS_}), sublevel(level, CohortLock.LEVEL), globalTicket, pre_, post_, currentThread)(op) {
		            open pre_();
		            assert atomic_spaces(?spaces);
				    if (mem(pair(append(ns, {CohortLock.NS_}), CohortLock_inv(lock)), spaces)) {
				        mem_map(pair(append(ns, {CohortLock.NS_}), CohortLock_inv(lock)), spaces, fst);
				        drop_append(ns, {CohortLock.TICKETLOCK_NS_});
				        drop_append(ns, {CohortLock.NS_});
				        forall_elim(map(fst, spaces), (is_prefix_of)(append(ns, {CohortLock.TICKETLOCK_NS_})), append(ns, {CohortLock.NS_}));
				        assert false;
				    }
				    drop_append(ns, {NS_});
				    drop_append(ns, {CohortLock.NS_});
				    if (mem(pair(append(ns, {Cohort.NS_}), Cohort_inv(this)), spaces)) {
				        mem_map(pair(append(ns, {Cohort.NS_}), Cohort_inv(this)), spaces, fst);
				        forall_elim(map(fst, spaces), (is_prefix_of)(append(ns, {CohortLock.TICKETLOCK_NS_})), append(ns, {Cohort.NS_}));
				        assert false;
				    }
		            open_atomic_space(append(ns, {Cohort.NS_}), Cohort_inv(this));
		            open Cohort_inv(this)();
		            match_has_at_<int>(globalOwnerHandle);
		            assert passing_global_owner_handle(?passingGlobalOwnerHandle);
		            
		            open_atomic_space(append(ns, {CohortLock.NS_}), CohortLock_inv(lock));
		            open CohortLock_inv(lock)();
		            match_has_at_(globalRoundInfoHandle);
		            match_has_at_(passingGlobalOwnerHandle);
		            merge_fractions this.owner |-> _;
		            merge_fractions this.held_ |-> _;
		            merge_fractions this._passing |-> _;
		            merge_fractions this._passCount |-> _;
		            merge_fractions this.ticketlock |-> _;
		            
		            int clientOwner = lock.clientOwner;
		            
		            {
		                predicate P_() = [1/2]lock.clientOwner |-> clientOwner &*& [1/2]lock.clientHeld |-> true;
		                predicate Q_() = [1/2]lock.clientOwner |-> clientOwner + 1 &*& [1/2]lock.clientHeld |-> false;
		                produce_lemma_function_pointer_chunk CohortLock_release_op(lock, clientOwner, P_, Q_)() {
		                    open P_();
		                    open lock.state(_, _);
		                    lock.clientOwner++;
		                    lock.clientHeld = false;
		                    close lock.state(_, _);
		                    close Q_();
		                } {
		                    close P_();
		                    assert is_CohortLock_release_op(?op_, _, _, _, _);
		                    is_prefix_of_append(ns, {}, {Cohort.NS_});
		                    is_prefix_of_append(ns, {}, {CohortLock.NS_});
							if (!forall(map(fst, spaces), (is_prefix_of)(ns))) {
								list<int> badName = not_forall(map(fst, spaces), (is_prefix_of)(ns));
								forall_elim(map(fst, spaces), (is_prefix_of)(append(ns, {CohortLock.TICKETLOCK_NS_})), badName);
								length_take_(length(ns) + 1, badName);
								append_drop_take(badName, length(append(ns, {CohortLock.TICKETLOCK_NS_})));
								assert badName == append(append(ns, {CohortLock.TICKETLOCK_NS_}), drop(length(ns) + 1, badName));
								append_assoc(ns, {CohortLock.TICKETLOCK_NS_}, drop(length(ns) + 1, badName));
								assert false;
							}
		                    ghop(op_);
		                    open Q_();
		                }
		            }
		            
		            op();
		            
		            lock.held_ = false;
		            lock.owner++;
		            
		            box ownerIncrBox = lock.ownerIncrBox;
		            consuming_box_predicate incr_box(ownerIncrBox, globalTicket)
		            perform_action incr() {}
		            producing_box_predicate incr_box(globalTicket + 1);
		            
		            assert growing_list<boolean>(notAloneListId, ?notAloneList);
		            if (length(notAloneList) == clientOwner) {
		                growing_list_add(notAloneListId, false);
		            }
		            
		            close CohortLock_inv(lock)();
		            close_atomic_space(append(ns, {CohortLock.NS_}), CohortLock_inv(lock));
		            
		            this._passing = false;
		            this._passCount = 0;
		            this.releasing = true;
		            
		            assert obs(_, ?p, ?clientObs);
		            
		            void *releaseSignal = create_signal();
		            init_signal(releaseSignal, sublevel(level, SIG_LEVEL));
		            growing_list_add(releaseSignalsId, releaseSignal);
		            create_has_at(releaseSignalsId, cohortTicket);
		            
		            close Cohort_inv(this)();
		            close_atomic_space(append(ns, {Cohort.NS_}), Cohort_inv(this));
		            assert obs(_, _, ?obs);
		            close post_(p, obs);
		            
		            level_subspace_lt_sublevels(level, CohortLock.LEVEL, SIG_LEVEL);
		            assert level_subspace_lt(sublevel(level, CohortLock.LEVEL), sublevel(level, SIG_LEVEL)) == true;
		            if (!forall(map(snd, clientObs), (level_subspace_lt)(sublevel(level, CohortLock.LEVEL)))) {
		                level badLevel = not_forall(map(snd, clientObs), (level_subspace_lt)(sublevel(level, CohortLock.LEVEL)));
		                forall_elim(map(snd, clientObs), (level_subspace_lt)(level), badLevel);
		                level_subspace_lt_sublevel(level, CohortLock.LEVEL, badLevel);
		                assert false;
		            }
		        };
		        @*/
		        //@ close pre_();
		        globalLock.release();
		        //@ open post_(_, _);
		    }
		    //@ assert post(?p, ?obs);
		    //@ assert has_at(?releaseSignalHandle, releaseSignalsId, cohortTicket, ?releaseSignal);
			{
		        /*@
		        predicate pre_() =
		            obs(currentThread, p, cons(pair(releaseSignal, sublevel(level, SIG_LEVEL)), obs)) &*&
		            has_at(releaseSignalHandle, releaseSignalsId, cohortTicket, releaseSignal) &*&
		            [_]this.lock |-> lock &*&
		            [_]this.globalOwnersId |-> globalOwnersId &*&
		            [_]this.releaseSignalsId |-> releaseSignalsId &*&
		            [_]this.ticketlock |-> ticketlock &*&
		            [_]lock.ns |-> ns &*&
		            [_]lock.level |-> level &*&
		            [_]lock.ticketlock |-> globalLock &*&
		            [_]lock.notAloneListId |-> notAloneListId &*&
		            [_]lock.roundsInfoId |-> roundsInfoId &*&
		            [_]atomic_space_(append(ns, {Cohort.NS_}), Cohort_inv(this)) &*&
		            [_]atomic_space_(append(ns, {CohortLock.NS_}), CohortLock_inv(lock)) &*&
					[1/4]this._passing |-> false &*& this.passing |-> false &*&
					[1/4]this._passCount |-> 0 &*& this.passCount |-> 0 &*&
					[1/8]this.held_ |-> true &*&
					[1/8]this.owner |-> cohortTicket &*&
					[1/2]this.releasing |-> true;
		        predicate post_(list<pathcomp> p_, list<pair<void *, level> > obs_) = p_ == p &*& obs_ == obs;
		        @*/
		        /*@
		        produce_lemma_function_pointer_chunk Ticketlock_release_ghost_op(ticketlock, append(ns, {Cohort.TICKETLOCK_NS_}), sublevel(level, Cohort.LEVEL), cohortTicket, pre_, post_, currentThread)(op) {
		            open pre_();
		            assert atomic_spaces(?spaces);
				    if (mem(pair(append(ns, {Cohort.NS_}), Cohort_inv(this)), spaces)) {
				        mem_map(pair(append(ns, {Cohort.NS_}), Cohort_inv(this)), spaces, fst);
				        forall_elim(map(fst, spaces), (is_prefix_of)(append(ns, {Cohort.TICKETLOCK_NS_})), append(ns, {Cohort.NS_}));
				        assert false;
				    }
		            open_atomic_space(append(ns, {Cohort.NS_}), Cohort_inv(this));
		            open Cohort_inv(this)();
		            
		            match_has_at_(releaseSignalHandle);
		            
		            op();
		            this.owner++;
		            this.held_ = false;
		            this.releasing = false;
		            
		            set_signal(releaseSignal);
		        
		            close Cohort_inv(this)();
		            close_atomic_space(append(ns, {Cohort.NS_}), Cohort_inv(this));
		            close post_(p, obs);
		            if (!forall(map(snd, obs), (level_subspace_lt)(sublevel(level, Cohort.LEVEL)))) {
		                level badLevel = not_forall(map(snd, obs), (level_subspace_lt)(sublevel(level, Cohort.LEVEL)));
		                forall_elim(map(snd, obs), (level_subspace_lt)(level), badLevel);
		                level_subspace_lt_sublevel(level, Cohort.LEVEL, badLevel);
		                assert false;
		            }
		        };
		        @*/
		        //@ close pre_();
				ticketlock.release();
				//@ open post_(_, _);
			}
		}
	}

}
