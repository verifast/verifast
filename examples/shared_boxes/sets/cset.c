#include "stdlib.h"
#include "cset.h"
#include "sset.h"
#include "threading.h"
#include "mutex3.h"
//@ #include "map.gh"
//@ #include "counting.gh"

struct cset {
    struct mutex3 *mutex;
    struct sset *set;
    struct mutex *cset_box_mutex;
    //@ box boxId;
    //@ list<int> res;
};

/*
    TODO: 
    1. currently acquire_own and release_own are not pure because they need to acquire the box mutex.
       use atomic actions instead of locking so that it is no longer necessary to use a box mutex.
       e.g. in the end, acquire_own, release_own and own_disjoint should be lemma's.
    2. own_disjoint does not release the mutex between the two actions. 
       actually, it should just do 1 action, but use the invariants of both handles.
*/



/*
   shared boxes vs cap:
   - cap_boxes can be split as long as they are stable. 
     shared_boxes can only be split into fractions.
     e.g. cap_box(...) = [_] shared_box(...)
   - cap_boxes can have a different predicate over time.
     shared_boxes always have the same predicate. When changes are necessary, it must be done using box parameters.
     to make sure that the clients have the correct predicate, a handle should specify the value of these parameters.
     e.g. cap_box(l, ?b ? x : y) -> b == true &*& cap_box(l, x)
          sha_box(l, ?b ? x : y) -> sha_box(l, ?b ? x : y) &*& btrue_handle(?h, l)
   - cap natively has a permission system.
     shared_boxes does not. They can be supported by storing the handle in a box parameter, and requiring that the action
     handle is the stored handle. Using some pure fact (e.g. x == 0) does not work because it does not guarantee stability.
     Maybe a helper field works (e.g. x->helper |-> _). This is a standard fractional permissions trick.
   - with cap, the actions always consume the corresponding permission. 
     with shared_boxes, the actions do not natively specify the handle that is required.  
     therefore, the client still needs to choose the correct handle. 
   - with cap, an action can release multiple permissions.
     shared_boxes can only produce one handle. 
     Of course, it is possible to create a union handle but this handle can only be split inside the box.
   - with cap, an action does not need to release a permission.
     shared_boxes always produce a handle, although it may be a dummy handle.
   - cap can conditionally release a different permission.
     shared_boxes always requires the production of one single handle. 
     It is of course possible to create a conditional handle.
   - in some sense, cap uses the permissions to modularize the state of the threads.
     shared_boxes need to maintain the state of all threads seperately inside the box.
    
   notes:
   - it may be necessary to support multiple handles (in the same way, multiple permissions can be necessary in cap).
     e.g. consuming a reservedhandle, and producing a reservedhandle and a changperm.
     
*/

/*@
//TODO: improve this definition
fixpoint bool eq_mod(list<int> l1, list<int> l2, int v) {
    return l2 == sorted_insert(v, l1) || l2 == remove_all2(v, l1) || l2 == l1;
}

lemma void eq_mod_mem(list<int> l1, list<int> l2, int v, int v2)
    requires eq_mod(l1, l2, v) == true &*& v != v2;
    ensures mem(v2, l1) == mem(v2, l2);
{
    switch(l1) {
        case nil:
        case cons(h, t):
            if(l2 == sorted_insert(v, l1)) {
                if(h < v) {
                    eq_mod_mem(t, sorted_insert(v, t), v, v2);
                }
            } else if(l2 == remove_all2(v, l1)) {
                eq_mod_mem(t, remove_all2(v, t), v, v2);
            } else {
            }
    }
}    
    
box_class cset_box(struct cset *s, bool locked, list<int> vs, map<int, handle> reserved, int changing_value) {
    invariant [1/2] s->set |-> ?set &*& 
        [1/2] s->mutex |-> ?mutex &*&
        [1/2] s->res |-> map_keys(reserved) &*&
        (locked ? mutex3_held(mutex) &*& map_contains_key(reserved, changing_value) == true : sset(set, vs));
        
    action observe();
        requires true;
        ensures locked == old_locked && vs == old_vs && reserved == old_reserved && changing_value == old_changing_value;
        
    action acquire_changeperm(int v);
        requires !map_contains_key(reserved, v);
        ensures reserved == map_put(old_reserved, v, actionHandle) &&
            locked == old_locked && vs == old_vs && changing_value == old_changing_value;

    action release_changeperm(int v); 
        requires map_contains_key(reserved, v) && actionHandle == map_get(reserved, v) && (locked ? changing_value != v : true); 
        ensures reserved == map_remove(old_reserved, v) &&
            locked == old_locked && vs == old_vs && changing_value == old_changing_value;
    
    action change(int v);
        requires !locked && map_contains_key(reserved, v) && actionHandle == map_get(reserved, v);
        ensures locked && vs == old_vs && reserved == old_reserved && changing_value == v;
        
    action gap(list<int> ws);
        requires locked && actionHandle == map_get(reserved, changing_value) && eq_mod(vs, ws, changing_value)==true;
        ensures !locked && vs == ws && reserved == old_reserved;
    
    
    handle_predicate changeperm(int val, bool m) {
        invariant 
            map_contains_key(reserved, val) && 
            map_get(reserved, val) == predicateHandle && 
            m == mem(val, vs) && 
            (locked ? changing_value != val : true);

        preserved_by observe() {
        }
        preserved_by acquire_changeperm(v) {
            map_put_invariant(old_reserved, val, v, actionHandle);
            map_contains_key_after_put(old_reserved, val, v, actionHandle);
        }
        preserved_by release_changeperm(v) {
            map_remove_invariant(old_reserved, val, v);
            map_contains_key_after_remove(old_reserved, val, v);
        }
        preserved_by change(v) {
        }
        preserved_by gap(ws) {
            if(old_changing_value != val) {
                eq_mod_mem(old_vs, ws, old_changing_value, val);
            }
        }
    }
    
    handle_predicate gapperm(int val, list<int> values) {
        invariant 
            map_contains_key(reserved, val) && 
            map_get(reserved, val) == predicateHandle && 
            val == changing_value && 
            locked && values == vs;
        
        preserved_by observe() {
        }
        preserved_by acquire_changeperm(v) {
            map_put_invariant(old_reserved, val, v, actionHandle);
            map_contains_key_after_put(old_reserved, val, v, actionHandle);
        }
        preserved_by release_changeperm(v) {
            map_contains_key_after_remove(old_reserved, val, v);
            map_remove_invariant(old_reserved, val, v);
        }
        preserved_by change(v) {
        }
        preserved_by gap(ws) {
        }
    }
    
    handle_predicate dummyhandle() { 
        invariant true;
        preserved_by observe() {
        }        
        preserved_by acquire_changeperm(v) {
        }
        preserved_by release_changeperm(v) {
        }
        preserved_by change(v) {
        }
        preserved_by gap(ws) {
        }
    }
}

lemma void changeperm_disjoint(handle h1, handle h2)
    requires changeperm(h1, ?boxId, ?v, ?b) &*& changeperm(h2, boxId, ?v2, ?b2);
    ensures changeperm(h1, boxId, v, b) &*& changeperm(h2, boxId, v2, b2) &*& h1 != h2;
{
    assume(false);
}
predicate_ctor cbm_inv(struct cset *s, box boxId) () = 
    cset_box(boxId, s, ?locked, ?values, ?reserved, ?changing);


predicate cset_internal(struct cset *s; box boxId) = 
    malloc_block_cset(s) &*&
    s->boxId |-> boxId &*&
    s->cset_box_mutex |-> ?cbm &*&
    mutex(cbm, cbm_inv(s, boxId)) &*&
    [1/2]s->mutex |-> ?mutex &*&
    [1/2]s->set |-> ?set &*&
    mutex3(mutex);

predicate cset(struct cset *s, list<int> res) = 
    counting(cset_internal, s, 1+length(res), ?boxId) &*&
    ticket(cset_internal, s, ?f) &*&
    [f] cset_internal(s, boxId) &*&
    [1/2] s->res |-> res;
    
predicate own (struct cset *s, int v, bool b) =
    ticket(cset_internal, s, ?f) &*&
    [f] cset_internal(s, ?boxId) &*& 
    changeperm(?h, boxId, v, b);
 
@*/

void own_disjoint(struct cset* s, int v)
    //@ requires own(s, v, ?b) &*& own(s, v, ?b2);
    //@ ensures false;
{
    //@ open own(s, v, b); 
    //@ assert changeperm(?h1, ?boxId, v, b);
    //@ open own(s, v, b2);
    //@ assert changeperm(?h2, boxId, v, b2);
    //@ changeperm_disjoint(h1, h2);
    //@ assert (h1 != h2);
    
    //@ open [?f]cset_internal(s, boxId);
    mutex_acquire(s->cset_box_mutex);
    //@ open cbm_inv(s, boxId)();
    
    /*@ consuming_box_predicate cset_box(boxId, s, ?locked, ?values, ?reserved, ?changing)
        consuming_handle_predicate changeperm(h1, v, b)
        perform_action observe() {
    @*/
    {
    }
    /*@
        }
        producing_box_predicate cset_box(s, locked, values, reserved, changing)
        producing_handle_predicate changeperm(v, b);
    @*/

    /*@ consuming_box_predicate cset_box(boxId, s, ?locked2, ?values2, ?reserved2, ?changing2)
        consuming_handle_predicate changeperm(h2, v, b2)
        perform_action observe() {
    @*/
    {
    }
    /*@
        }
        producing_box_predicate cset_box(s, locked2, values2, reserved2, changing2)
        producing_handle_predicate changeperm(v, b2);
    @*/

    //@ close cbm_inv(s, boxId)();
    mutex_release(s->cset_box_mutex);
}

 
void acquire_own(struct cset* s, int v)
    //@ requires cset(s, ?vs) &*& !mem(v, vs);
    //@ ensures cset(s, snoc(vs, v)) &*& own(s, v, ?b);
{
    //@ open cset(s, vs);
    //@ open [?f]cset_internal(s, ?boxId);
    mutex_acquire(s->cset_box_mutex);
    //@ open cbm_inv(s, boxId)();
    
    //@ handle h = create_handle cset_box_handle(boxId);
    /*@ consuming_box_predicate cset_box(boxId, s, ?locked, ?values, ?reserved, ?changing)
        consuming_handle_predicate cset_box_handle(h)
        perform_action acquire_changeperm(v) {
    @*/
    {
        //@ map_contains_key_mem_map_keys(reserved, v);
        //@ s->res = snoc(vs, v); 
        //@ map_put_map_keys(reserved, v, h);        
        //@ map_put_map_contains_key(reserved, v, h);
        //@ map_put_map_get(reserved, v, h);
        //@ if(locked) map_contains_key_after_put(reserved, changing, v, h);
    }
    /*@
        }
        producing_box_predicate cset_box(s, locked, values, map_put(reserved, v, h), changing)
        producing_handle_predicate changeperm(v, mem(v, values));
    @*/
    //@ close cbm_inv(s, boxId)();
    mutex_release(s->cset_box_mutex);
    //@ create_ticket(cset_internal, s);
    //@ close own(s, v, mem(v, values));
    //@ close [f] cset_internal(s, boxId);
    //@ close cset(s, snoc(vs, v)); 
}

void release_own(struct cset* s, int v)
    //@ requires cset(s, ?vs) &*& own(s, v, ?b);
    //@ ensures cset(s, remove(v, vs));
{
    //@ open cset(s, vs);
    //@ open [?f]cset_internal(s, ?boxId);
    //@ open own(s, v, b);
    //@ destroy_ticket(cset_internal, s);
    mutex_acquire(s->cset_box_mutex);
    //@ open cbm_inv(s, boxId)();
        
    /*@ consuming_box_predicate cset_box(boxId, s, ?locked, ?values, ?reserved, ?changing)
        consuming_handle_predicate changeperm(?h, v, b)
        perform_action release_changeperm(v) {
    @*/
    {
        //@ map_contains_key_mem_map_keys(reserved, v);
        //@ s->res = remove(v, vs);
        //@ map_remove_map_keys(reserved, v);
        //@ if(locked) map_contains_key_after_remove(reserved, changing, v);
    }
    /*@
        }
        producing_box_predicate cset_box(s, locked, values, map_remove(reserved, v), changing)
        producing_handle_predicate cset_box_handle();
    @*/
    //@ leak cset_box_handle(h, boxId);
    //@ close cbm_inv(s, boxId)();
    mutex_release(s->cset_box_mutex);

    //@ close [f] cset_internal(s, boxId);
    //@ close cset(s, remove(v, vs)); 
}

struct cset* ccreate() 
    //@ requires true;
    //@ ensures cset(result, nil);
{
    struct cset* r = malloc(sizeof(struct cset));
    if(r==0) abort();
    struct sset* s = screate();
    r->set = s;
    struct mutex3* m = create_mutex3();
    mutex3_release(m);
    r->mutex = m;
    //@ r->res = nil;
    //@ create_box boxId = cset_box(r, false, nil, mnil, 0);
    //@ r->boxId = boxId;
    //@ close cbm_inv(r, boxId)();
    //@ close create_mutex_ghost_arg(cbm_inv(r, boxId));
    struct mutex* cbm = create_mutex();
    r->cset_box_mutex = cbm;
    //@ close cset_internal(r, boxId);
    //@ start_counting(cset_internal, r);
    //@ create_ticket(cset_internal, r);
    //@ close cset(r, nil);
    return r;
}

void cdispose(struct cset* s)
    //@ requires cset(s, nil);
    //@ ensures true;
{
    //@ open cset(s, nil);
    //@ destroy_ticket(cset_internal, s);
    //@ stop_counting(cset_internal, s);
    //@ open cset_internal(s, ?boxId);
    mutex_dispose(s->cset_box_mutex);
    mutex3_acquire(s->mutex);
    //@ open cbm_inv(s, boxId)();
    //@ dispose_box cset_box(boxId, s, ?waslocked, ?b, ?c, ?d);
    //@ if(waslocked) mutex3_exclusive(s->mutex);
    mutex3_dispose(s->mutex);
    sdispose(s->set);
    free(s);
    
}

void cadd(struct cset* s, int v) 
    //@ requires own(s, v, ?b) &*& v > INT_MIN &*& v < INT_MAX;
    //@ ensures own(s, v, true);
{
    //@ open own(s, v, b);
    //@ open [?f]cset_internal(s, ?boxId);
    mutex3_acquire(s->mutex);

    mutex_acquire(s->cset_box_mutex);
    //@ open cbm_inv(s, boxId)();
    /*@
        consuming_box_predicate cset_box(boxId, s, ?locked, ?values, ?reserved, ?changing)
        consuming_handle_predicate changeperm(?h, v, b)
        perform_action change(v) {
    @*/
    {
        //@ if(locked) mutex3_exclusive(s->mutex);
    }
    /*@
        }
        producing_box_predicate cset_box(s, true, values, reserved, v)
        producing_handle_predicate gapperm(v, values);
    @*/
    //@ close cbm_inv(s, boxId)();
    mutex_release(s->cset_box_mutex);
    
    sadd(s->set, v);
    
    mutex_acquire(s->cset_box_mutex);
    //@ open cbm_inv(s, boxId)();
    /*@
        consuming_box_predicate cset_box(boxId, s, ?locked2, ?values2, ?reserved2, ?changed2)
        consuming_handle_predicate gapperm(h, v, values)
        perform_action gap(sorted_insert(v, values)) {
    @*/
    {
        //@ sorted_insert_mem(v, values);
    }
    /*@
        }
        producing_box_predicate cset_box(s, false, sorted_insert(v, values), reserved2, changed2)
        producing_handle_predicate changeperm(v, true);
    @*/
    //@ close cbm_inv(s, boxId)();
    mutex_release(s->cset_box_mutex);
    
    
    mutex3_release(s->mutex);
 
    //@ close [f]cset_internal(s, boxId);
    //@ close own(s, v, true);
}

void cremove(struct cset* s, int v) 
    //@ requires own(s, v, ?b) &*& v > INT_MIN &*& v < INT_MAX;
    //@ ensures own(s, v, false);
{
    //@ open own(s, v, b);
    //@ open [?f]cset_internal(s, ?boxId);
    mutex3_acquire(s->mutex);

    mutex_acquire(s->cset_box_mutex);
    //@ open cbm_inv(s, boxId)();
    /*@
        consuming_box_predicate cset_box(boxId, s, ?locked, ?values, ?reserved, ?changing)
        consuming_handle_predicate changeperm(?h, v, b)
        perform_action change(v) {
    @*/
    {
        //@ if(locked) mutex3_exclusive(s->mutex);
    }
    /*@
        }
        producing_box_predicate cset_box(s, true, values, reserved, v)
        producing_handle_predicate gapperm(v, values);
    @*/
    //@ close cbm_inv(s, boxId)();
    mutex_release(s->cset_box_mutex);
    
    sremove(s->set, v);
    
    mutex_acquire(s->cset_box_mutex);
    //@ open cbm_inv(s, boxId)();
    /*@
        consuming_box_predicate cset_box(boxId, s, ?locked2, ?values2, ?reserved2, ?changed2)
        consuming_handle_predicate gapperm(h, v, values)
        perform_action gap(remove_all2(v, values)) {
    @*/
    {
        //@ remove_all2_mem(v, v, values);
    }
    /*@
        }
        producing_box_predicate cset_box(s, false, remove_all2(v, values), reserved2, changed2)
        producing_handle_predicate changeperm(v, false);
    @*/
    //@ close cbm_inv(s, boxId)();
    mutex_release(s->cset_box_mutex);
    
    
    mutex3_release(s->mutex);
 
    //@ close [f]cset_internal(s, boxId);
    //@ close own(s, v, false);
}


bool ccontains(struct cset* s, int v) 
    //@ requires own(s, v, ?b) &*& v > INT_MIN &*& v < INT_MAX;
    //@ ensures own(s, v, b) &*& b == result;
{
    //@ open own(s, v, b);
    //@ open [?f]cset_internal(s, ?boxId);
    mutex3_acquire(s->mutex);

    mutex_acquire(s->cset_box_mutex);
    //@ open cbm_inv(s, boxId)();
    /*@
        consuming_box_predicate cset_box(boxId, s, ?locked, ?values, ?reserved, ?changing)
        consuming_handle_predicate changeperm(?h, v, b)
        perform_action change(v) {
    @*/
    {
        //@ if(locked) mutex3_exclusive(s->mutex);
    }
    /*@
        }
        producing_box_predicate cset_box(s, true, values, reserved, v)
        producing_handle_predicate gapperm(v, values);
    @*/
    //@ close cbm_inv(s, boxId)();
    mutex_release(s->cset_box_mutex);
    
    bool result = scontains(s->set, v);
    //@ assert result == b;
    
    mutex_acquire(s->cset_box_mutex);
    //@ open cbm_inv(s, boxId)();
    /*@
        consuming_box_predicate cset_box(boxId, s, ?locked2, ?values2, ?reserved2, ?changed2)
        consuming_handle_predicate gapperm(h, v, values)
        perform_action gap(values) {
    @*/
    {
    }
    /*@
        }
        producing_box_predicate cset_box(s, false, values, reserved2, changed2)
        producing_handle_predicate changeperm(v, result);
    @*/
    //@ close cbm_inv(s, boxId)();
    mutex_release(s->cset_box_mutex);
    
    mutex3_release(s->mutex);
 
    //@ close [f]cset_internal(s, boxId);
    //@ close own(s, v, result);
    return result;
}



/* @
predicate_family critical_section_pre(void *body)(predicate() inv);
predicate_family critical_section_post(void *body)();

typedef void critical_section_body();
    requires critical_section_pre(this)(?inv) &*& inv();
    ensures critical_section_post(this)() &*& inv();
    
lemma void ghost_critical_section(struct mutex *mutex);
    requires [?f]mutex(mutex, ?inv) &*& critical_section_pre(?body)(inv) &*& is_critical_section_body(body) == true;
    ensures [f]mutex(mutex, inv) &*& critical_section_post(body)();
@*/