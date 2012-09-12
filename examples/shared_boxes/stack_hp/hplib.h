#ifndef HPLIB_H
#define HPLIB_H

/*
    A library to support hazard poitners. 
*/

#include "atomics.h"
//@ #include "ghost_params.gh"
//@ #include "lset.gh"
//@ #include "cperm_ex2.gh"

struct hpuser;

struct hprec;

/*
TODO:
- allow user invariants about the users
- do I really need the removed objects?
- allow user to configure gc threshold
- allow user to configure local hazard pointer data structure
- allow user to maintain a pool of free nodes by extending object_destructor

TODO: Make generic garbage collector:
- store destructor inside manager, user or hprec
- allow separate objects for each hazard pointer
- use the same manager/users to protect multiple data structures

*/

/*@

//1. predicates that are released into the local state of a thread. 

//a hazard pointer user which is opened. The _hp predicate provides information about the hazard pointer and 
//the _removed predicate provides information about the removed object.
predicate hpuser_open(struct hpuser* user, int allUsersId, list<struct hprec*> released);
predicate hpuser_hprec(struct hprec* rec; void* hp, bool validated);
predicate hpuser_rem(struct hpuser* user; void* removed);
predicate hpuser_ret(struct hpuser* user; list<void*> retired);

//a hazard pointer user which is not used by the thread. (e.g. between 2 operations of the data structure)
predicate hpuser(struct hpuser* user, int allUsersId) =
    hpuser_open(user, allUsersId, nil) &*&
    hpuser_rem(user, 0) &*&
    hpuser_ret(user, _);

//2. the predicate that is inside the atomic space + the sep/unsep pair.
predicate hpmanager(struct hpuser** head_ptr, int* hpcount_ptr, int allUsersId, void* object_lem, list<void*> reachable, list<void*> retired, list<void*> removed, list<struct hpuser*> users);

predicate_family hpmanager_sep  (void *sep)  (any args, struct hpuser** head_ptr, int* hpcount_ptr, int allUsersId, void* object_lem, predicate() inv, hpmanager_unsep *unsep);
predicate_family hpmanager_unsep(void *unsep)(any args, struct hpuser** head_ptr, int* hpcount_ptr, int allUsersId, void* object_lem, predicate() inv, hpmanager_sep *sep, list<void*> reachable, list<void*> retired, list<void*> removed, list<struct hpuser*> users);

typedef lemma void hpmanager_sep();
    requires hpmanager_sep(this)(?args, ?hp, ?cp, ?id, ?object, ?inv, ?unsep) &*& inv();
    ensures hpmanager_unsep(unsep)(args, hp, cp, id, object, inv, this, ?reachable, ?retired, ?removed, ?users) &*& hpmanager(hp, cp, id, object, reachable, retired, removed, users);

typedef lemma void hpmanager_unsep();
    requires hpmanager_unsep(this)(?args, ?hp, ?cp, ?id, ?object, ?inv, ?sep, ?reachable, ?retired, ?removed, ?users) &*& hpmanager(hp, cp, id, object, reachable, retired, removed, users);
    ensures hpmanager_sep(sep)(args, hp, cp, id, object, inv, this) &*& inv();

predicate hpmanager_inv_info(any args, struct hpuser** head_ptr, int* hpcount_ptr, int allUsersId, void* object_lem, predicate() inv, hpmanager_sep* sep, hpmanager_unsep* unsep) = 
    hpmanager_sep(sep)(args, head_ptr, hpcount_ptr, allUsersId, object_lem, inv, unsep) &*&
    is_hpmanager_sep(sep) &*& is_hpmanager_unsep(unsep);


@*/

//initializing and disposing the hazard pointer manager
void init_hpmanager(struct hpuser** head_ptr, int* hpcount_ptr);
//@ requires ghost_params<void*>(?objlem) &*& pointer(head_ptr, _) &*& integer(hpcount_ptr, _);
//@ ensures hpmanager(head_ptr, hpcount_ptr, _, objlem, nil, nil, nil, nil);

void dispose_hpmanager(struct hpuser** head_ptr, object_destructor* destructor);
/*@ requires hpmanager(head_ptr, ?hpcount_ptr, ?id, ?objlem, nil, _, _, nil) &*&
        object_destructor_inv(destructor)(objlem) &*&
        is_object_destructor(destructor) == true; 
@*/
/*@ ensures pointer(head_ptr, _) &*& integer(hpcount_ptr, _) &*&
        object_destructor_inv(destructor)(objlem) &*&
        is_object_destructor(destructor) == true;
@*/

//acquiring and releasing the hazard pointer user

/*@

predicate_family hpmanager_acquire_user_context_pre(void *ctxt)(hpmanager_unsep* unsep, any args);
predicate_family hpmanager_acquire_user_context_post(void *ctxt)(any args);

typedef lemma void hpmanager_acquire_user_context(list<struct hpuser*> users1, struct hpuser* user, list<struct hpuser*> users2);
    requires
        hpmanager_acquire_user_context_pre(this)(?unsep, ?args) &*&
        hpmanager_unsep(unsep)(args, ?hp, ?cp, ?id, ?object, ?inv, ?sep, ?reachable, ?retired, ?removed, append(users1, users2));
    ensures
        hpmanager_unsep(unsep)(args, hp, cp, id, object, inv, sep, reachable, retired, removed, append(users1, cons(user, users2))) &*&
        hpmanager_acquire_user_context_post(this)(args);
@*/
struct hpuser* acquire_hpuser(struct hpuser** head_ptr, int* hpcount_ptr);
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

/*@

predicate_family hpmanager_release_user_context_pre(void *ctxt)(hpmanager_unsep* unsep, any args);
predicate_family hpmanager_release_user_context_post(void *ctxt)(any args);

typedef lemma void hpmanager_release_user_context(list<struct hpuser*> users1, struct hpuser* user, list<struct hpuser*> users2);
    requires
        hpmanager_release_user_context_pre(this)(?unsep, ?args) &*&
        hpmanager_unsep(unsep)(args, ?hp, ?cp, ?id, ?object, ?inv, ?sep, ?reachable, ?retired, ?removed, append(users1, cons(user, users2)));
    ensures
        hpmanager_unsep(unsep)(args, hp, cp, id, object, inv, sep, reachable, retired, removed, append(users1, users2)) &*&
        hpmanager_release_user_context_post(this)(args);
@*/

void release_hpuser(struct hpuser* user);
/*@ requires 
        hpmanager_inv_info(?args, ?head_ptr, ?hpcount_ptr, ?id, ?objlem, ?inv, ?sep, ?unsep) &*&
        is_hpmanager_release_user_context(?lem) &*&
        hpmanager_release_user_context_pre(lem)(unsep, args) &*& 
        [?f]atomic_space(inv) &*& 
        hpuser(user, id);
@*/
/*@ ensures 
        hpmanager_inv_info(args, head_ptr, hpcount_ptr, id, objlem, inv, sep, unsep) &*&
        is_hpmanager_release_user_context(lem) &*&
        hpmanager_release_user_context_post(lem)(args) &*& 
        [f]atomic_space(inv);
@*/

// acquiring and releasing hazard pointers

struct hprec* acquire_hprec(struct hpuser* user);
/*@ requires 
        hpmanager_inv_info(?args, ?hp, ?cp, ?id, ?objlem, ?inv, ?sep, ?unsep) &*&
        [?f]atomic_space(inv) &*& 
        hpuser_open(user, id, ?released);
@*/
/*@ ensures 
        hpmanager_inv_info(args, hp, cp, id, objlem, inv, sep, unsep) &*&
        [f]atomic_space(inv) &*& 
        hpuser_hprec(result, 0, false) &*&
        hpuser_open(user, id, lset_add(released, result)) &*&
        !lset_contains(released, result);
@*/

void release_hprec(struct hpuser* user, struct hprec* rec);
/*@ requires 
        hpmanager_inv_info(?args, ?hp, ?cp, ?id, ?objlem, ?inv, ?sep, ?unsep) &*&
        [?f]atomic_space(inv) &*& 
        hpuser_hprec(rec, 0, false) &*&
        hpuser_open(user, id, ?released) &*&
        lset_contains(released, rec) == true;
@*/
/*@ ensures 
        hpmanager_inv_info(args, hp, cp, id, objlem, inv, sep, unsep) &*&
        [f]atomic_space(inv) &*& 
        hpuser_open(user, id, lset_remove(released, rec));
@*/

// lemma to insert an object into the reachable nodes
/*@

lemma void insert_object(void* obj);
    requires 
        hpmanager(?hptr, ?cptr, ?id, ?objlem, ?reachable, ?retired, ?popped, ?users) &*&
        is_object_set_trackerId(objlem) &*&
        object(objlem)(obj, _, ?data);
    ensures 
        is_object_set_trackerId(objlem) &*&
        hpmanager(hptr, cptr, id, objlem, cons(obj, reachable), retired, popped, users) &*&
        object_fraction(objlem, obj, data, _);
    
lemma void validate_hazard_pointer(struct hprec* rec);
    requires 
        hpmanager(?hptr, ?cptr, ?id, ?objlem, ?reachable, ?retired, ?popped, ?users) &*&
        hpuser_open(?user, id, ?released) &*&
        lset_contains(released, rec) == true &*&
        hpuser_hprec(rec, ?hp, false) &*&
        hp != 0 &*&
        lset_contains(reachable, hp) == true;
    ensures 
        hpmanager(hptr, cptr, id, objlem, reachable, retired, popped, users) &*& 
        hpuser_open(user, id, released) &*&
        hpuser_hprec(rec, hp, true) &*&
        object_fraction(objlem, hp, _, _);

lemma void release_hazard_pointer(struct hprec* rec);
    requires 
        hpmanager(?hptr, ?cptr, ?id, ?objlem, ?reachable, ?retired, ?popped, ?users) &*&
        hpuser_open(?user, id, ?released) &*&
        lset_contains(released, rec) == true &*&
        hpuser_hprec(rec, ?hp, true) &*&
        object_fraction(objlem, hp, _, _);
    ensures 
        hpmanager(hptr, cptr, id, objlem, reachable, retired, popped, users) &*& 
        hpuser_open(user, id, released) &*&
        hpuser_hprec(rec, hp, false);

lemma void free_object_not_registered(void* obj);
    requires 
        hpmanager(?hptr, ?cptr, ?id, ?objlem, ?reachable, ?retired, ?popped, ?users) &*&
        object(objlem)(obj, ?tid, ?data);
    ensures
        hpmanager(hptr, cptr, id, objlem, reachable, retired, popped, users) &*& 
        object(objlem)(obj, tid, data) &*&
        !lset_contains(reachable, obj) &*&
        !lset_contains(retired, obj) &*&
        !lset_contains(popped, obj);
@*/

// setting and resetting hazard pointers
void set_hazard_pointer(struct hprec *rec, void* hp);
/*@ requires 
        hpmanager_inv_info(?args, ?hptr, ?cptr, ?id, ?objlem, ?inv, ?sep, ?unsep) &*&
        [?f]atomic_space(inv) &*& 
        hpuser_open(?user, id, ?released) &*&
        lset_contains(released, rec) == true &*&
        hpuser_hprec(rec, ?prev, ?valid) &*&
        ( valid ? object_fraction(objlem, prev, _, _) : true );
@*/
/*@ ensures
        hpmanager_inv_info(args, hptr, cptr, id, objlem, inv, sep, unsep) &*&
        [f]atomic_space(inv) &*& 
        hpuser_open(user, id, released) &*&
        hpuser_hprec(rec, hp, false);
@*/

void reset_hazard_pointer(struct hprec *rec);
/*@ requires 
        hpmanager_inv_info(?args, ?hptr, ?cptr, ?id, ?objlem, ?inv, ?sep, ?unsep) &*&
        [?f]atomic_space(inv) &*& 
        hpuser_open(?user, id, ?released) &*&
        lset_contains(released, rec) == true &*&
        hpuser_hprec(rec, ?prev, ?valid) &*&
        ( valid ? object_fraction(objlem, prev, _, _) : true );
@*/
/*@ ensures
        hpmanager_inv_info(args, hptr, cptr, id, objlem, inv, sep, unsep) &*&
        [f]atomic_space(inv) &*& 
        hpuser_open(user, id, released) &*&
        hpuser_hprec(rec, 0, false);
@*/


// destructors for objects

//
///*@ 
//predicate_family object_destructor_pre  (void *destructor)(any args, void* objlem);
//predicate_family object_destructor_post (void *destructor)(any args, void* objlem, void* obj);
// @*/
//typedef void object_destructor(void* obj);
//    //@ requires object_destructor_pre(this)(?args, ?lem) &*& object(lem)(obj, _, _);
//    //@ ensures object_destructor_post(this)(args, lem, obj);

/*@ 
predicate_family object_destructor_inv(void *destructor)(void* objlem);

@*/

typedef void object_destructor(void* obj);
    //@ requires object_destructor_inv(this)(?objlem) &*& object(objlem)(obj, _, _);
    //@ ensures object_destructor_inv(this)(objlem);



// retiring removed objects (+ garbage collecting retired objects after a certain treshold has been exceeded)

void retire_object(struct hpuser* user, void* removed, object_destructor* destructor);
/*@ requires 
        hpmanager_inv_info(?args, ?hptr, ?cptr, ?id, ?objlem, ?inv, ?sep, ?unsep) &*&
        [?f]atomic_space(inv) &*& 
        hpuser_open(user, id, ?released) &*&
        hpuser_rem(user, removed) &*&
	hpuser_ret(user, _) &*&
        removed != 0 &*&
        object_destructor_inv(destructor)(objlem) &*&
        is_object_destructor(destructor) == true;
@*/
/*@ ensures
        hpmanager_inv_info(args, hptr, cptr, id, objlem, inv, sep, unsep) &*&
        [f]atomic_space(inv) &*& 
        hpuser_open(user, id, released) &*&
        hpuser_rem(user, 0) &*&
	hpuser_ret(user, _) &*&
        object_destructor_inv(destructor)(objlem) &*&
        is_object_destructor(destructor) == true;
@*/

// forcing garbage collection of retired objects

void gc(struct hpuser* user, object_destructor* destructor);
/*@ requires 
        hpmanager_inv_info(?args, ?hptr, ?cptr, ?id, ?objlem, ?inv, ?sep, ?unsep) &*&
        [?f]atomic_space(inv) &*& 
        hpuser(user, id) &*&
        object_destructor_inv(destructor)(objlem) &*&
        is_object_destructor(destructor) == true;
@*/
/*@ ensures
        hpmanager_inv_info(args, hptr, cptr, id, objlem, inv, sep, unsep) &*&
        [f]atomic_space(inv) &*& 
        hpuser(user, id) &*&
        object_destructor_inv(destructor)(objlem) &*&
        is_object_destructor(destructor) == true;
@*/

#endif

