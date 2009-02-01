#include "stdlib.h"

struct lock;

/*@
predicate lock(struct lock *lock, predicate() inv);

lemma void lock_fractions_split(struct lock *lock, real coef);
    requires [?f]lock(lock, ?a) &*& 0 < coef &*& coef < 1;
    ensures [coef * f]lock(lock, a) &*& [(1 - coef) * f]lock(lock, a);

lemma void lock_fractions_merge(struct lock *lock);
    requires [?f1]lock(lock, ?a1) &*& [?f2]lock(lock, ?a2);
    ensures [f1 + f2]lock(lock, a1) &*& a2 == a1;

predicate create_lock_ghost_arg(predicate() inv)
    requires inv();

@*/

struct lock *create_lock();
    //@ requires create_lock_ghost_arg(?a);
    //@ ensures lock(result, a);

void lock_acquire(struct lock *lock);
    //@ requires [?f]lock(lock, ?a);
    //@ ensures [f]lock(lock, a) &*& a();

void lock_release(struct lock *lock);
    //@ requires [?f]lock(lock, ?a) &*& a();
    //@ ensures [f]lock(lock, a);

void lock_dispose(struct lock *lock);
    //@ requires lock(lock, ?a);
    //@ ensures a();

/*@

predicate_family thread_run_pre(void *thread_run)(void *data, any info);
predicate_family thread_run_post(void *thread_run)(void *data, any info);

@*/

typedef void (* thread_run)(void *data);
    //@ requires thread_run_pre(this)(data, ?info);
    //@ ensures thread_run_post(this)(data, info);

struct thread;

/*@
predicate thread(struct thread *thread, void *thread_run, void *data, any info);
@*/

struct thread *thread_start(void *run, void *data);
    //@ requires is_thread_run(run) == true &*& thread_run_pre(run)(data, ?info);
    //@ ensures thread(result, run, data, info);
    
void thread_join(struct thread *thread);
    //@ requires thread(thread, ?run, ?data, ?info);
    //@ ensures thread_run_post(run)(data, info);

struct sum {
    int sum;
};

struct session {
    struct sum *sum_object;
    struct lock *lock;
};

/*@
inductive handle_option = handle_option_none | handle_option_some(handle);

box_class contrib_box(int contrib, handle_option owner) {

    action set_value(int contrib0);
        requires owner == handle_option_none || owner == handle_option_some(actionHandle);
        ensures contrib == contrib0 && owner == handle_option_some(actionHandle);

    handle_predicate contrib_handle(int handleContrib) {
        invariant owner == handle_option_some(predicateHandle) && contrib == handleContrib;
        
        preserved_by set_value(contrib0) {}
    }
}

predicate_ctor sum(struct sum *sumObject, box box1, box box2)()
    requires
        sumObject->sum |-> ?sum &*&
        contrib_handle(_, box1, ?contrib1) &*&
        contrib_handle(_, box2, sum - contrib1) &*&
        0 <= contrib1 &*& contrib1 <= 1 &*&
        0 <= sum - contrib1 &*& sum - contrib1 <= 1;

inductive contribute_info = contribute_info(box, box, box, struct sum *, struct lock *);

predicate_family_instance thread_run_pre(contribute)(struct session *session, contribute_info info)
    requires
        switch (info) {
            case contribute_info(box1, box2, thisBox, sumObject, lock):
                return contribute_pre(session, box1, box2, thisBox, sumObject, lock);
        };

predicate contribute_pre(struct session *session, box box1, box box2, box thisBox, struct sum *sumObject, struct lock *lock)
    requires
        session->sum_object |-> sumObject &*& session->lock |-> lock &*& malloc_block_session(session) &*&
        [1/2]lock(lock, sum(sumObject, box1, box2)) &*& (thisBox == box1 || thisBox == box2) &*& contrib_box(thisBox, 0, _);

predicate_family_instance thread_run_post(contribute)(struct session *session, contribute_info info)
    requires
        switch (info) {
            case contribute_info(box1, box2, thisBox, sumObject, lock):
                return [1/2]lock(lock, sum(sumObject, box1, box2)) &*& contrib_box(thisBox, 1, _);
        };

@*/

void contribute(void *data) //@ : thread_run
{
    //@ open thread_run_pre(contribute)(data, _);
    struct session *session = data;
    //@ open contribute_pre(session, ?box1, ?box2, ?thisBox, _, _);
    struct lock *lock = session->lock;
    struct sum *sumObject = session->sum_object;
    free(session);
    lock_acquire(lock);
    //@ open sum(sumObject, box1, box2)();
    int sum = sumObject->sum;
    //@ if (thisBox == box1) {} else {}
    /*@
    consuming_box_predicate contrib_box(thisBox, 0, _)
    consuming_handle_predicate contrib_handle(?thisHandle, _)
    perform_action set_value(1) {
    }
    producing_box_predicate contrib_box(1, handle_option_some(thisHandle))
    producing_handle_predicate contrib_handle(1);
    @*/
    sumObject->sum = sum + 1;
    //@ close sum(sumObject, box1, box2)();
    lock_release(lock);
    //@ close thread_run_post(contribute)(session, contribute_info(box1, box2, thisBox, sumObject, lock));
}

int main()
    //@ requires true;
    //@ ensures true;
{
    struct sum *sumObject = malloc(sizeof(struct sum));
    if (sumObject == 0) {
        abort();
    }
    sumObject->sum = 0;
    //@ box box1 = create_contrib_box(0, handle_option_none);
    //@ handle handle1 = create_contrib_box_handle(box1);
    /*@
    consuming_box_predicate contrib_box(box1, 0, handle_option_none)
    consuming_handle_predicate contrib_box_handle(handle1)
    perform_action set_value(0)
    {
    }
    producing_box_predicate contrib_box(0, handle_option_some(handle1))
    producing_handle_predicate contrib_handle(0);
    @*/
    //@ box box2 = create_contrib_box(0, handle_option_none);
    //@ handle handle2 = create_contrib_box_handle(box2);
    /*@
    consuming_box_predicate contrib_box(box2, 0, handle_option_none)
    consuming_handle_predicate contrib_box_handle(handle2)
    perform_action set_value(0)
    {
    }
    producing_box_predicate contrib_box(0, handle_option_some(handle2))
    producing_handle_predicate contrib_handle(0);
    @*/
    //@ close sum(sumObject, box1, box2)();
    //@ close create_lock_ghost_arg(sum(sumObject, box1, box2));
    struct lock *lock = create_lock();
    //@ lock_fractions_split(lock, 1/2);
    
    struct session *session1 = malloc(sizeof(struct session));
    if (session1 == 0) {
        abort();
    }
    session1->sum_object = sumObject;
    session1->lock = lock;
    //@ close contribute_pre(session1, box1, box2, box1, sumObject, lock);
    //@ close thread_run_pre(contribute)(session1, contribute_info(box1, box2, box1, sumObject, lock));
    struct thread *thread1 = thread_start(contribute, session1);
    
    struct session *session2 = malloc(sizeof(struct session));
    if (session2 == 0) {
        abort();
    }
    session2->sum_object = sumObject;
    session2->lock = lock;
    //@ close contribute_pre(session2, box1, box2, box2, sumObject, lock);
    //@ close thread_run_pre(contribute)(session2, contribute_info(box1, box2, box2, sumObject, lock));
    struct thread *thread2 = thread_start(contribute, session2);
    
    thread_join(thread1);
    //@ open thread_run_post(contribute)(session1, contribute_info(box1, box2, box1, sumObject, lock));
    
    thread_join(thread2);
    //@ open thread_run_post(contribute)(session2, contribute_info(box1, box2, box2, sumObject, lock));
    
    //@ lock_fractions_merge(lock);
    lock_dispose(lock);
    //@ open sum(sumObject, box1, box2)();
    
    // The following perform_action statement is only to show contrib_handle(_, box1, 1)
    /*@
    consuming_box_predicate contrib_box(box1, 1, ?owner1)
    consuming_handle_predicate contrib_handle(?box1handle, _)
    perform_action set_value(1) {}
    producing_box_predicate contrib_box(1, owner1)
    producing_handle_predicate contrib_box_handle();
    @*/
    //@ leak contrib_box(box1, _, _) &*& contrib_box_handle(_, box1);
    
    // The following perform_action statement is only to show contrib_handle(_, box2, 1)
    /*@
    consuming_box_predicate contrib_box(box2, 1, ?owner2)
    consuming_handle_predicate contrib_handle(?box2handle, _)
    perform_action set_value(1) {}
    producing_box_predicate contrib_box(1, owner2)
    producing_handle_predicate contrib_box_handle();
    @*/
    //@ leak contrib_box(box2, _, _) &*& contrib_box_handle(_, box2);
    
    int sum = sumObject->sum;
    assert(sum == 2);
    free(sumObject);

    return 0;
}
