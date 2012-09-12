#include "hplib.h"
#include "stdlib.h"
#include "atomics.h"
#include "atomics_int.h"
#include "linkedlist.h"
//@ #include "raw_ghost_lists.gh"
//@ #include "ghost_lists.gh"
//@ #include "lmultisetandset.gh"




/*
TODOS:
- change type of hpuser->active and hprec->active to bool
- make distinct ghost_set that has precise member handle and use it to make hpuser_open precise
- add invariant hpCount >= length(flatten(allHps));
*/

void foo() 
//@ requires true;
//@ ensures false;
{
	//TODO: i did not complete this file yet.
}

struct hprec {
    void* active;
    struct hprec* next;
    void* hp; //the hazard pointer of this user (zero if unused)
    //@ bool validated; //whether the hazard pointer was validated 
};

    // @ void* datastructure; //the data structure that is protected by this hpuser
struct hpuser {

    void* active; //whether this hpuser is currently used by a thread
    struct hpuser* next; //the next stack client
    
    struct linkedlist* rlist; //the linked list that contains the retired objects of this thread 
    //@ list<void*> retired; // the retired objects of this thread
    
    struct hprec* hprecs;
    
    //@ void* removed; //the node that is popped by this hpuser (zero if unused) 
    
    //@ bool localHpActive; //whether this user is currently collecting the hazard pointers of other users
    //@ list<struct hpuser*> localHpRemUsers; //the remaining users for which the hazard pointers must be collected. 
    //@ bool localHpFirstCollected; //whether the hazard pointer of the first remaining user is collected. 
    //@ list<void*> localHpList; //the local hazard pointers
};

/*@

predicate hprec_precursor(struct hprec *rec; struct hprec* next) =
    rec != 0 &*&
    malloc_block_hprec(rec) &*&
    rec->active |-> (void*)1 &*& 
    rec->next |-> next &*&
    rec->hp |-> 0 &*&
    rec->validated |-> false;

predicate hprec_atomic(struct hprec *rec; bool active, struct hprec* next, void* hp, bool validated) =
    rec != 0 &*&
    malloc_block_hprec(rec) &*&
    [1/2]rec->active |-> ?activeP &*&
    active == (activeP != (void*)0) &*&
    [1/2]rec->next |-> next &*&
    [1/2]rec->hp |-> hp &*&
    [1/2]rec->validated |-> validated &*&
    (validated ? hp != 0 : true) &*&
    (active ?
        true :
        [1/2]rec->active |-> _ &*&
        [1/2]rec->next |-> _ &*&
        [1/2]rec->hp |-> _ &*&
        [1/2]rec->validated |-> _
    );

predicate hprec_list_atomic(struct hprec *from, struct hprec *to; list<struct hprec*> allHpRecs, list<struct hprec*> activeHpRecs, list<void*> hps) = 
    from == to ?
        allHpRecs == nil &*&
        activeHpRecs == nil &*&
        hps == nil 
    :
        hprec_atomic(from, ?active, ?next, ?hp, ?validated) &*&
        hprec_list_atomic(next, to, ?allHpRecs0, ?activeHpRecs0, ?hps0) &*&
        allHpRecs == cons(from, allHpRecs0) &*&
        activeHpRecs == (active ? cons(from, activeHpRecs0) : activeHpRecs0) &*&
        hps == (active && validated ? cons(hp, hps0) : hps0);

predicate hprec_client(struct hprec *rec; bool active, struct hprec* next) =
    rec != 0 &*&
    [1/4]rec->active |-> ?activeP &*&
    active == (activeP != (void*)0) &*&
    [1/2]rec->next |-> next &*& 
    (active ? true : [1/4]rec->active |-> _);

predicate hprec_list_client(struct hprec *from, struct hprec *to; list<struct hprec*> allHpRecs, list<struct hprec*> activeHpRecs) = 
    from == to ?
        allHpRecs == nil &*&
        activeHpRecs == nil 
    :
        hprec_client(from, ?active, ?next) &*& 
        hprec_list_client(next, to, ?allHpRecs0, ?activeHpRecs0) &*&
        allHpRecs == cons(from, allHpRecs0) &*&
        activeHpRecs == (active ? cons(from, activeHpRecs0) : activeHpRecs0);

predicate hpuser_precursor(struct hpuser *user; struct hpuser* next) =
    user != 0 &*&
    malloc_block_hpuser(user) &*&
    user->active |-> (void*)1 &*& 
    user->next |-> next &*&
    user->rlist |-> ?rlist &*&
    linkedlist(rlist, nil) &*&
    user->retired |-> nil &*&
    user->hprecs |-> 0 &*&
    user->removed |-> (void*)0 &*&
    user->localHpActive |-> false &*&
    user->localHpRemUsers |-> nil &*&
    user->localHpFirstCollected |-> false &*&
    user->localHpList |-> nil;

predicate hpuser_atomic(struct hpuser *user, int allUsersId, bool active, struct hpuser *next, list<void*> hps, void* removed, list<void*> retired, bool hpActive, list<struct hpuser*> hpRem, bool fcc, list<void*> hpList) =
    user != 0 &*&
    malloc_block_hpuser(user) &*&
    [_]ghost_list_member_handle(allUsersId, user) &*&
    [1/2]user->active |-> ?activeP &*&
    active == (activeP != (void*)0) &*& 
    user->next |-> next &*&
    [1/2]user->retired |-> retired &*&
    [1/2]user->hprecs |-> ?rec &*&
    hprec_list_atomic(rec, 0, ?allHpRecs, ?activeHpRecs, hps) &*&
    [1/2]user->removed |-> removed &*&
    [1/2]user->localHpActive |-> hpActive &*&
    [1/2]user->localHpRemUsers |-> hpRem &*&
    [1/2]user->localHpFirstCollected |-> fcc &*&
    [1/2]user->localHpList |-> hpList &*&
    (active ? 
        true
    :
        [1/2]user->active |-> _ &*&
        activeHpRecs == nil &*&
        hps == nil &*&
        [1/2]user->retired |-> _ &*&
        [1/2]user->hprecs |-> _ &*&
        [1/2]user->removed |-> 0 &*&
        [1/2]user->localHpActive |-> false &*&
        [1/2]user->localHpRemUsers |-> nil &*&
        [1/2]user->localHpFirstCollected |-> false &*&
        [1/2]user->localHpList |-> nil &*&
        user->rlist |-> ?rlist &*&
        linkedlist(rlist, retired) &*&
        hprec_list_client(rec, 0, _, nil)
    );

inductive hpRec = hpRec(list<struct hpuser*>, list<void*>, list<void*>, bool);
fixpoint list<struct hpuser*> remClients(hpRec r) { switch(r) { case hpRec(rem, valid, hps, first): return rem; } }
fixpoint list<void*> validNodes(hpRec r) { switch(r) { case hpRec(rem, valid, hps, first): return valid; } }
fixpoint list<void*> hpNodes(hpRec r) { switch(r) { case hpRec(rem, valid, hps, first): return hps; } }
fixpoint bool firstCollected(hpRec r) { switch(r) { case hpRec(rem, valid, hps, first): return first; } }

predicate hpuser_list_atomic(struct hpuser *from, struct hpuser *to, int allUsersId, list<struct hpuser*> allUsers, list<struct hpuser*> activeUsers, list<list<void*> > allHps, list<void*> allRemoved, list<list<void*> > allRetired, list<hpRec> hpRecs) =
    from == to ?
        allUsers == nil &*&
        activeUsers == nil &*&
        allHps == nil  &*&
        allRemoved == nil &*&
        allRetired == nil &*&
        hpRecs == nil   
    :
        hpuser_atomic(from, allUsersId, ?active, ?next, ?hps, ?removed, ?retired, ?hpActive, ?hpRem, ?hpFcc, ?hpList) &*&
        hpuser_list_atomic(next, to, allUsersId, ?allUsers0, ?activeUsers0, ?allHps0, ?allRemoved0, ?allRetired0, ?hpRecs0) &*&
        allUsers == cons(from, allUsers0) &*&
        activeUsers == (active ? cons(from, activeUsers0) : activeUsers0) &*&
        allHps == cons(hps, allHps0)&*&
        allRemoved == (removed == 0 ? allRemoved0 : cons(removed, allRemoved0)) &*&
        allRetired == cons(retired, allRetired0) &*&
        hpRecs == (hpActive ? cons(hpRec(hpRem, retired, hpList, hpFcc), hpRecs0) : hpRecs0);

predicate hpuser_open(struct hpuser* user, int allUsersId, list<struct hprec*> released) = 
    user != 0 &*&
    [_]ghost_list_member_handle(allUsersId, user) &*&
    [1/2]user->active |-> (void*)1  &*& 
    [1/2]user->hprecs |-> ?rec &*&
    hprec_list_client(rec, 0, _, released) &*&
    [1/2]user->localHpActive |-> false &*&
    [1/2]user->localHpRemUsers |-> nil &*&
    [1/2]user->localHpFirstCollected |-> false &*&
    [1/2]user->localHpList |-> nil;
predicate hpuser_hprec(struct hprec* rec; void* hp, bool validated) = 
    [1/4]rec->active |-> (void*)1 &*&
    [1/2]rec->hp |-> hp &*&
    [1/2]rec->validated |-> validated &*&
    (validated ? hp != 0 : true);
predicate hpuser_rem(struct hpuser* user; void* removed) = 
    [1/2]user->removed |-> removed;
predicate hpuser_ret(struct hpuser* user; list<void*> retired) = 
    [1/2]user->retired |-> retired &*&
    user->rlist |-> ?rlist &*&
    linkedlist(rlist, retired);


predicate_ctor object_tracker_helper(void* objlem, list<void*> allocNodes, int extra)(void* node) =
    object_tracker(objlem, node, occ(allocNodes, node) + extra, _);

//TODO: update validLhp
predicate validLhp(list<struct hpuser*> allUsers, list<list<void*> > allHps, list<void*> retired, list<struct hpuser*> lhpRem, list<void*> lhpValid, list<void*> lhp, bool fcc) =
    length(allUsers) == length(allHps) &*&
    length(lhpRem) <= length(allUsers) &*&
    (fcc ? lhpRem != nil : true) &*& 
    lhpRem == drop(length(allUsers) - length(lhpRem), allUsers) &*& 
    !mem((void*)0, lhpValid) &*&
    lset_subset(lhpValid, retired) == true &*&
    lset_subset(lset_inters(flatten(take(length(allHps) - length(lhpRem) + (fcc ? 1 : 0), allHps)), lhpValid), lset_inters(lhp, lhpValid)) == true;

predicate_ctor validLhp_helper(list<struct hpuser*> allUsers, list<list<void*> > allHps, list<void*> retired)(hpRec lhpR) = 
    validLhp(allUsers, allHps, retired, remClients(lhpR), validNodes(lhpR), hpNodes(lhpR), firstCollected(lhpR));

predicate hpmanager(struct hpuser** headp, int* cptr, int allUsersId, void* object_lem, list<void*> reachable, list<void*> retired, list<void*> removed, list<struct hpuser*> users) =
    pointer(headp, ?head) &*&
    integer(cptr, ?hpCount) &*& hpCount >= 0 &*&
    hpuser_list_atomic(head, 0, allUsersId, ?allUsers, users, ?allHps, removed, ?allRetired, ?hpRecs) &*&
    ghost_list(allUsersId, allUsers) &*&
    retired == flatten(allRetired) &*&
    foreach(reachable, object_tracker_helper(object_lem, flatten(allHps), 1)) &*&
    foreach(removed, object_tracker_helper(object_lem, flatten(allHps), 0)) &*&
    foreach(retired, object_tracker_helper(object_lem, flatten(allHps), 0)) &*&
    foreach(hpRecs, validLhp_helper(allUsers, allHps, retired)) &*&
    lset_subset(flatten(allHps), lset_union(reachable, lset_union(removed, retired))) == true;
    
//NOTE: distinct, disjoint,

//lemma's
lemma void hprec_list_atomic_inactive(struct hprec* rec)
    requires hprec_list_atomic(rec, 0, ?allHpRecs, nil, ?hps);
    ensures hprec_list_atomic(rec, 0, allHpRecs, nil, hps) &*& hps == nil;
{
    if(rec == 0) {
        open hprec_list_atomic(rec, 0, allHpRecs, nil, hps);
        close hprec_list_atomic(rec, 0, allHpRecs, nil, hps);
    } else {
        open hprec_list_atomic(rec, 0, allHpRecs, nil, hps);
        assert hprec_atomic(rec, ?active, ?next, _, _);
        hprec_list_atomic_inactive(next);
        close hprec_list_atomic(rec, 0, allHpRecs, nil, hps);
    }
}
lemma void hpuser_list_atomic_inactive(struct hpuser* user)
    requires hpuser_list_atomic(user, 0, ?id, ?allUsers, nil, ?allHps, ?removed, ?retired, ?hpRecs);
    ensures hpuser_list_atomic(user, 0, id, allUsers, nil, allHps, removed, retired, hpRecs) &*& removed == nil &*& hpRecs == nil &*& flatten(allHps) == nil;
{
    if(user == 0) {
        open hpuser_list_atomic(user, 0, id, allUsers, nil, allHps, removed, retired, hpRecs);
        close hpuser_list_atomic(user, 0, id, allUsers, nil, allHps, removed, retired, hpRecs);
    } else {
        open hpuser_list_atomic(user, 0, id, allUsers, nil, allHps, removed, retired, hpRecs);
        open hpuser_atomic(user, id, ?active, ?next, _, _, _, _, _, _, _);
        struct hprec* rec = user->hprecs;
        hprec_list_atomic_inactive(rec);
        close hpuser_atomic(user, id, false, next, _, _, _, _, _, _, _);
        hpuser_list_atomic_inactive(next);
        close hpuser_list_atomic(user, 0, id, allUsers, nil, allHps, removed, retired, hpRecs);
    }
}

lemma void hpuser_list_atomic_last_nomem(struct hpuser *first, struct hpuser *last)
    requires hpuser_list_atomic(first, last, ?id, ?allUsers, ?activeUsers, ?allHps, ?removed, ?retired, ?hpRecs);
    ensures hpuser_list_atomic(first, last, id, allUsers, activeUsers, allHps, removed, retired, hpRecs) &*& !mem(last, allUsers);
{
    open hpuser_list_atomic(first, last, id, _, _, _, _, _, _);
    if(first == last) {
    } else {
        assert hpuser_atomic(first, id, ?active, ?next, _, _, _, _, _, _, _);
        hpuser_list_atomic_last_nomem(next, last);
    }
    close hpuser_list_atomic(first, last, id, _, _, _, _, _, _);
}

lemma void hpuser_list_atomic_split(struct hpuser *first, struct hpuser *last, struct hpuser *user)
    requires hpuser_list_atomic(first, last, ?id, ?allUsers, ?activeUsers, ?allHps, ?removed, ?retired, ?hpRecs) &*& mem(user, allUsers) == true;
    ensures hpuser_list_atomic(first, user, id, ?allUsers1, ?activeUsers1, ?allHps1, ?removed1, ?retired1, ?hpRecs1) &*& 
            hpuser_list_atomic(user, last, id, ?allUsers2, ?activeUsers2, ?allHps2, ?removed2, ?retired2, ?hpRecs2) &*& 
        allUsers == append(allUsers1, allUsers2) &*& 
        activeUsers == append(activeUsers1, activeUsers2) &*& 
        allHps == append(allHps1, allHps2) &*&
        removed == append(removed1, removed2) &*&
        retired == append(retired1, retired2) &*&
        hpRecs == append(hpRecs1, hpRecs2) &*& 
        !mem(user, allUsers1) &*&
        !mem(last, allUsers1);
{
    if(first == last) {
        open hpuser_list_atomic(first, last, id, allUsers, activeUsers, allHps, removed, retired, hpRecs);
        assert false; 
    } else {
        open hpuser_list_atomic(first, last, id, allUsers, activeUsers, allHps, removed, retired, hpRecs);
        if(first == user) {
            close hpuser_list_atomic(first, last, id, allUsers, activeUsers, allHps, removed, retired, hpRecs);
            close hpuser_list_atomic(first, first, id, _, _, _, _, _, _);
        } else {
            assert hpuser_atomic(first, id, ?active, ?next, _, _, _, _, _, _, _);
            hpuser_list_atomic_split(next, last, user);
            close hpuser_list_atomic(first, user, id, _, _, _, _, _, _);
        }
    }
}


lemma void hpuser_list_atomic_join(struct hpuser *first, struct hpuser *last)
    requires hpuser_list_atomic(first, ?user, ?id, ?allUsers1, ?activeUsers1, ?allHps1, ?removed1, ?retired1, ?hpRecs1) &*& 
            hpuser_list_atomic(user, last, id, ?allUsers2, ?activeUsers2, ?allHps2, ?removed2, ?retired2, ?hpRecs2) &*&
            !mem(last, allUsers1);
    ensures hpuser_list_atomic(first, last, id, append(allUsers1, allUsers2), append(activeUsers1, activeUsers2), append(allHps1, allHps2), append(removed1, removed2), append(retired1, retired2), append(hpRecs1, hpRecs2));
{
    open hpuser_list_atomic(first, user, id, _, _, _, _, _, _);
    if(first == user) {
    } else {
        assert hpuser_atomic(first, id, ?active, ?next, _, _, _, _, _, _, _);
        hpuser_list_atomic_join(next, last);
        close hpuser_list_atomic(first, last, id, _, _, _, _, _, _);
    }
}



@*/


void init_hpmanager(struct hpuser** head_ptr, int* hpcount_ptr)
//@ requires ghost_params<void*>(?objlem) &*& pointer(head_ptr, _) &*& integer(hpcount_ptr, _);
//@ ensures hpmanager(head_ptr, hpcount_ptr, _, objlem, nil, nil, nil, nil);
{
    *hpcount_ptr = 0;
    *head_ptr = 0;
    //@ open ghost_params(objlem);
    //@ int id = create_ghost_list();
    //@ close hpuser_list_atomic(0, 0, id, nil, nil, nil, nil, nil, nil);
    //@ close foreach(nil, object_tracker_helper(objlem, nil, 1));
    //@ close foreach(nil, object_tracker_helper(objlem, nil, 0));
    //@ close foreach(nil, object_tracker_helper(objlem, nil, 0));
    //@ close foreach(nil, validLhp_helper(nil, nil, nil));
    //@ close hpmanager(head_ptr, hpcount_ptr, _, objlem, nil, nil, nil, nil);
}

/*@

    
@*/

void dispose_hpmanager(struct hpuser** head_ptr, object_destructor* destructor)
/*@ requires hpmanager(head_ptr, ?hpcount_ptr, ?id, ?objlem, nil, _, _, nil) &*&
        object_destructor_inv(destructor)(objlem) &*&
        is_object_destructor(destructor) == true; 
@*/
/*@ ensures pointer(head_ptr, _) &*& integer(hpcount_ptr, _) &*&
        object_destructor_inv(destructor)(objlem) &*&
        is_object_destructor(destructor) == true;
@*/
{
    //@ open hpmanager(head_ptr, hpcount_ptr, id, objlem, nil, _, _, nil);
    struct hpuser* user = *head_ptr;
    //@ hpuser_list_atomic_inactive(user);
    //@ assert hpuser_list_atomic(user, 0, id, ?allUsers, nil, ?allHps, nil, ?retired, nil) &*& flatten(allHps) == nil;
    //@ open foreach(nil, object_tracker_helper(objlem, nil, 1));
    //@ open foreach(nil, validLhp_helper(allUsers, allHps, flatten(retired)));
    //@ open foreach(nil, object_tracker_helper(objlem, nil, 0));
    
    while(user != 0) 
    /*@ invariant hpuser_list_atomic(user, 0, id, ?remUsers, nil, ?remHps, nil, ?remRetired, nil) &*& flatten(remHps) == nil &*&
            foreach(flatten(remRetired), object_tracker_helper(objlem, nil, 0)) &*& object_destructor_inv(destructor)(objlem) &*&
            is_object_destructor(destructor) == true;
    @*/
    {
        //@ open hpuser_list_atomic(user, 0, id, remUsers, nil, remHps, nil, remRetired, nil);
        //@ open hpuser_atomic(user, id, ?active, ?unext, _, _, ?retired2, _, _, _, _);
        struct linkedlist* rlist = user->rlist;
        //@ assert linkedlist(rlist, retired2);
        //@ foreach_split(retired2, flatten(tail(remRetired)));
        while(!linkedlist_is_empty(rlist)) 
        /*@ invariant linkedlist(rlist, ?retired3) &*& foreach(retired3, object_tracker_helper(objlem, nil, 0)) &*& object_destructor_inv(destructor)(objlem) &*&
            is_object_destructor(destructor) == true;
        @*/
        {
            void* o = linkedlist_pop(rlist);
            //@ open foreach(retired3, object_tracker_helper(objlem, nil, 0));
            //@ open object_tracker_helper(objlem, nil, 0)(o);
            //@ destroy_object_tracker(o);
            destructor(o);
        }
        //@ open foreach(nil, object_tracker_helper(objlem, nil, 0));
        linkedlist_dispose(rlist);
        
        struct hprec* hprec = user->hprecs;
        //@ assert hprec_list_atomic(hprec, 0, ?allHpRecs, nil, ?hps);
        while(hprec != 0) 
        //@ invariant hprec_list_atomic(hprec, 0, ?remHpRecs, nil, hps) &*& hprec_list_client(hprec, 0, _, nil);
        {
            //@ open hprec_list_atomic(hprec, 0, remHpRecs, nil, hps);
            //@ open hprec_list_client(hprec, 0, _, nil);
            //@ open hprec_atomic(hprec, ?hprecActive, _, ?hp, ?validated);
            //@ open hprec_client(hprec, _, _);
            //@ assert !hprecActive; 
            struct hprec* next = hprec->next;
            free(hprec);
            hprec = next;
        }
        //@ open hprec_list_atomic(hprec, 0, remHpRecs, nil, hps);
        //@ open hprec_list_client(hprec, 0, _, nil);
        //@ assert hps == nil;
        
        struct hpuser* next = user->next;        
        free(user);
        user = next;
    }
    //@ open hpuser_list_atomic(user, 0, id, remUsers, nil, remHps, nil, remRetired, nil);
    //@ open foreach(nil, object_tracker_helper(objlem, nil, 0));
    //@ assert flatten(allHps) == nil;
    //@ leak ghost_list(id, allUsers);
}






struct hpuser* get_first_user(struct hpuser **head_ptr)
/*@ requires 
        hpmanager_inv_info(?args, head_ptr, ?cptr, ?id, ?objlem, ?inv, ?sep, ?unsep) &*&
        [?f]atomic_space(inv);
@*/
/*@ ensures 
        hpmanager_inv_info(args, head_ptr, cptr, id, objlem, inv, sep, unsep) &*&
        [f]atomic_space(inv) &*& 
        (result != 0 ? [_]ghost_list_member_handle(id, result) : true);
@*/
{
    struct hpuser *user = 0;
    //@ struct hpuser *userProphecy = create_prophecy_pointer();
    {
        /*@
        predicate_family_instance atomic_load_pointer_context_pre(context)(predicate() inv2, void **pp, void *prophecy) =
            inv2 == inv &*&
            pp == head_ptr &*& 
            prophecy == userProphecy &*&
            hpmanager_inv_info(args, head_ptr, cptr, id, objlem, inv, sep, unsep);
        predicate_family_instance atomic_load_pointer_context_post(context)() = 
            hpmanager_inv_info(args, head_ptr, cptr, id, objlem, inv, sep, unsep) &*&
            userProphecy != 0 ? [_]ghost_list_member_handle(id, userProphecy) : true ;
        lemma void context(atomic_load_pointer_operation *op) : atomic_load_pointer_context
            requires
                atomic_load_pointer_context_pre(context)(?inv2, ?pp, ?prophecy) &*& inv2() &*&
                is_atomic_load_pointer_operation(op) &*& atomic_load_pointer_operation_pre(op)(pp, prophecy);
            ensures
                atomic_load_pointer_context_post(context)() &*& inv2() &*&
                is_atomic_load_pointer_operation(op) &*& atomic_load_pointer_operation_post(op)();
        {
            open atomic_load_pointer_context_pre(context)(inv2, pp, prophecy);
            open hpmanager_inv_info(args, head_ptr, cptr, id, objlem, inv, sep, unsep);
            sep();
            open hpmanager(head_ptr, cptr, id, objlem, ?reachable, ?retired, ?removed, ?users);
            op();
            open hpuser_list_atomic(userProphecy, 0, id, _, _, _, _, _, _);
            if(userProphecy != 0) {
                open hpuser_atomic(userProphecy, _, _, _, _, _, _, _, _, _, _);
                close hpuser_atomic(userProphecy, _, _, _, _, _, _, _, _, _, _);
            } 
            close hpuser_list_atomic(userProphecy, 0, id, _, _, _, _, _, _);
            close hpmanager(head_ptr, cptr, id, objlem, reachable, retired, removed, users);
            unsep();
            close hpmanager_inv_info(args, head_ptr, cptr, id, objlem, inv, sep, unsep);
            close atomic_load_pointer_context_post(context)();
        }
        @*/
        //@ close atomic_load_pointer_context_pre(context)(inv, head_ptr, userProphecy);
        //@ produce_lemma_function_pointer_chunk(context);
        user = atomic_load_pointer(head_ptr);
        //@ open atomic_load_pointer_context_post(context)();
        //@ leak is_atomic_load_pointer_context(context);
    }
    return user;
}

struct hpuser* get_next_user(struct hpuser* user)
/*@ requires 
        hpmanager_inv_info(?args, ?hptr, ?cptr, ?id, ?objlem, ?inv, ?sep, ?unsep) &*&
        [?f]atomic_space(inv) &*&
        [_]ghost_list_member_handle(id, user) &*& user != 0;
@*/
/*@ ensures 
        hpmanager_inv_info(args, hptr, cptr, id, objlem, inv, sep, unsep) &*&
        [f]atomic_space(inv) &*& 
        (result != 0 ? [_]ghost_list_member_handle(id, result) : true);
@*/
{
    struct hpuser *next;
    //@ struct hpuser *nextProphecy = create_prophecy_pointer();
    {
        /*@
        predicate_family_instance atomic_load_pointer_context_pre(context)(predicate() inv2, void **pp, void *prophecy) =
            inv2 == inv &*&
            pp == &user->next &*& 
            prophecy == nextProphecy &*&
            hpmanager_inv_info(args, hptr, cptr, id, objlem, inv, sep, unsep) &*&
            user != 0 &*&
            [_]ghost_list_member_handle(id, user);
        predicate_family_instance atomic_load_pointer_context_post(context)() = 
            hpmanager_inv_info(args, hptr, cptr, id, objlem, inv, sep, unsep) &*&
            (nextProphecy == 0 ? true : [_]ghost_list_member_handle(id, nextProphecy));
        lemma void context(atomic_load_pointer_operation *op) : atomic_load_pointer_context
            requires
                atomic_load_pointer_context_pre(context)(?inv2, ?pp, ?prophecy) &*& inv2() &*&
                is_atomic_load_pointer_operation(op) &*& atomic_load_pointer_operation_pre(op)(pp, prophecy);
            ensures
                atomic_load_pointer_context_post(context)() &*& inv2() &*&
                is_atomic_load_pointer_operation(op) &*& atomic_load_pointer_operation_post(op)();
        {
            open atomic_load_pointer_context_pre(context)(inv2, pp, prophecy);
            open hpmanager_inv_info(args, hptr, cptr, id, objlem, inv, sep, unsep);
            sep();
            open hpmanager(hptr, cptr, id, objlem, _, _, _, _);
            ghost_list_member_handle_lemma();
            assert pointer(hptr, ?h);
            hpuser_list_atomic_split(h, 0, user);
            open hpuser_list_atomic(user, 0, id, _, _, _, _, _, _);
            open hpuser_atomic(user, id, _, _, _, _, _, _, _, _, _);
            op();
            open hpuser_list_atomic(nextProphecy, 0, id, _, _, _, _, _, _);
            if(nextProphecy != 0) {
                open hpuser_atomic(nextProphecy, id, _, _, _, _, _, _, _, _, _);
                close hpuser_atomic(nextProphecy, id, _, _, _, _, _, _, _, _, _);
            }
            close hpuser_list_atomic(nextProphecy, 0, id, _, _, _, _, _, _);
            close hpuser_atomic(user, id, _, _, _, _, _, _, _, _, _);
            close hpuser_list_atomic(user, 0, id, _, _, _, _, _, _);
            hpuser_list_atomic_join(h, 0);            
            close hpmanager(hptr, cptr, id, objlem, _, _, _, _);
            unsep();
            close hpmanager_inv_info(args, hptr, cptr, id, objlem, inv, sep, unsep);
            close atomic_load_pointer_context_post(context)();
        }
        @*/
        //@ close atomic_load_pointer_context_pre(context)(inv, &user->next, nextProphecy);
        //@ produce_lemma_function_pointer_chunk(context);
        next = atomic_load_pointer(&user->next);
        //@ open atomic_load_pointer_context_post(context)();
        //@ leak is_atomic_load_pointer_context(context);
    }
    return next;
}


bool try_acquire_hpuser(struct hpuser* user)
/*@ requires 
        hpmanager_inv_info(?args, ?hptr, ?cptr, ?id, ?objlem, ?inv, ?sep, ?unsep) &*&
        [?f]atomic_space(inv) &*&
        [_]ghost_list_member_handle(id, user) &*& user != 0;
@*/
/*@ ensures 
        hpmanager_inv_info(args, hptr, cptr, id, objlem, inv, sep, unsep) &*&
        [f]atomic_space(inv) &*& 
        (result ? hpuser(user, id) : [_]ghost_list_member_handle(id, user));
@*/
{
    void *casResult = 0;
    //@ void *casResultProphecy = create_prophecy_pointer();
    {
        /*@
        predicate_family_instance atomic_compare_and_store_pointer_context_pre(context)(predicate() inv2, void **pp, void *old, void *new, void *prophecy) = 
            inv2 == inv &*& 
            pp == &user->active &*& 
            old == (void*)0 &*& 
            new == (void*)1 &*& 
            prophecy == casResultProphecy &*& //end of argument fixing
            hpmanager_inv_info(args, hptr, cptr, id, objlem, inv, sep, unsep) &*&
            [_]ghost_list_member_handle(id, user);
        predicate_family_instance atomic_compare_and_store_pointer_context_post(context)() = 
            hpmanager_inv_info(args, hptr, cptr, id, objlem, inv, sep, unsep) &*&
            [_]ghost_list_member_handle(id, user) &*&
            casResultProphecy == (void*)0 ? 
                hpuser(user, id) : 
                true; 
        lemma void context(atomic_compare_and_store_pointer_operation *op):atomic_compare_and_store_pointer_context
            requires
                atomic_compare_and_store_pointer_context_pre(context)(?inv2, ?pp, ?old, ?new, ?prophecy) &*& inv2() &*&
                is_atomic_compare_and_store_pointer_operation(op) &*&
                atomic_compare_and_store_pointer_operation_pre(op)(pp, old, new, prophecy);
            ensures
                atomic_compare_and_store_pointer_context_post(context)() &*& inv2() &*&
                is_atomic_compare_and_store_pointer_operation(op) &*&
                atomic_compare_and_store_pointer_operation_post(op)();
        {
            open atomic_compare_and_store_pointer_context_pre(context)(inv2, pp, old, new, prophecy);
            open hpmanager_inv_info(args, hptr, cptr, id, objlem, inv, sep, unsep);
            sep();
            open hpmanager(hptr, cptr, id, objlem, ?reachable, ?retired, ?removed, ?users);
            //assert stack->clients |-> ?ch &*& clients(ch, 0, allClientsId, stack, ?allClients, ?allocNodes, ?poppedNodes, ?retiredNodes, ?hpLists);
            ghost_list_member_handle_lemma();
            assert pointer(hptr, ?h);
            hpuser_list_atomic_split(h, 0, user);
            //struct hpuser *from, struct hpuser *to, int allUsersId, list<struct hpuser*> allUsers, list<struct hpuser*> activeUsers, list<list<void*> > allHps, list<void*> allRemoved, list<list<void*> > allRetired, list<hpRec> hpRecs
            assert hpuser_list_atomic(h, user, id, ?allUsers1, ?activeUsers1, ?allHps1, ?allRemoved1, ?allRetired1, ?hpRecs1);
            open hpuser_list_atomic(user, 0, id, _, _, _, _, _, _);
            open hpuser_atomic(user, id, ?active, ?nextuser, ?hps, ?uremoved, ?uretired, ?hpActive, ?hpRem, ?fcc, ?hpList);
            assert hpuser_list_atomic(nextuser, 0, id, ?allUsers2, ?activeUsers2, ?allHps2, ?allRemoved2, ?allRetired2, ?hpRecs2);
            
            op();
            if(casResultProphecy == (void*) 0) {
                assert !active;
                assert !hpActive &*& hpRem == nil &*& !fcc &*& hpList == nil &*& uremoved == 0;
                close hpuser_open(user, id, nil);
                close hpuser(user, id);
            }
            close hpuser_atomic(user, id, _, _, _, _, _, _, _, _, _);
            close hpuser_list_atomic(user, 0, id, _, _, _, _, _, _);
            hpuser_list_atomic_join(h, 0);            
            close hpmanager(hptr, cptr, id, objlem, reachable, retired, removed, append(activeUsers1, cons(user, activeUsers2)));
            unsep();
            close hpmanager_inv_info(args, hptr, cptr, id, objlem, inv, sep, unsep);
            close atomic_compare_and_store_pointer_context_post(context)();
        }
        @*/
        //@ close atomic_compare_and_store_pointer_context_pre(context)(inv, &user->active, (void*)0, (void*)1, casResultProphecy);
        //@ produce_lemma_function_pointer_chunk(context);
        casResult = atomic_compare_and_store_pointer(&user->active, (void*)0, (void*)1);
        //@ open atomic_compare_and_store_pointer_context_post(context)();
        //@ leak is_atomic_compare_and_store_pointer_context(context);
    }

    
    return casResult == (void*)0;
}


struct hpuser* acquire_hpuser(struct hpuser** head_ptr, int* hpcount_ptr)
/*@ requires 
        hpmanager_inv_info(?args, head_ptr, hpcount_ptr, ?id, ?objlem, ?inv, ?sep, ?unsep) &*&
        is_hpmanager_acquire_user_context(?lem) &*&
        hpmanager_acquire_user_context_pre(lem)(unsep, args) &*& 
        [?f]atomic_space(inv);
@*/
/*@ ensures 
        hpmanager_inv_info(args, head_ptr, hpcount_ptr, id, objlem, inv, sep, unsep) &*&
        is_hpmanager_acquire_user_context(lem) &*&
        hpmanager_acquire_user_context_post(lem)(args) &*& 
        [f]atomic_space(inv) &*& 
        hpuser(result, id);
@*/
{
    struct hpuser *user = get_first_user(head_ptr);
    bool acquired = false;
    while(user != 0 && !acquired)
    /*@ invariant 
            hpmanager_inv_info(args, head_ptr, hpcount_ptr, id, objlem, inv, sep, unsep) &*&
            is_hpmanager_acquire_user_context(lem) &*&
            [f]atomic_space(inv) &*&
            (user != 0 ? [_]ghost_list_member_handle(id, user) : true) &*&
            (acquired ? hpmanager_acquire_user_context_post(lem)(args) &*& hpuser(user, id) : hpmanager_acquire_user_context_pre(lem)(unsep, args) );
    @*/
    {
        //acquired = try_acquire_stack_client(stack, sc);
        if(!acquired)
            user = get_next_user(user);
    }

    return user;
}
