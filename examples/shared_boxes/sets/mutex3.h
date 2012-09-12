#ifndef MUTEX3_H
#define MUTEX3_H

struct mutex3;

/*@
predicate mutex3(struct mutex3 *mutex;);

predicate mutex3_held(struct mutex3 *mutex;);

lemma void mutex3_exclusive(struct mutex3 *mutex);
    requires mutex3_held(mutex) &*& mutex3_held(mutex);
    ensures false;
@*/

struct mutex3 *create_mutex3();
    //@ requires true;
    //@ ensures mutex3(result) &*& mutex3_held(result);
    
void mutex3_acquire(struct mutex3 *mutex);
    //@ requires [?f]mutex3(mutex);
    //@ ensures [f]mutex3(mutex) &*& mutex3_held(mutex);

void mutex3_release(struct mutex3 *mutex);
    //@ requires mutex3_held(mutex);
    //@ ensures true;

void mutex3_dispose(struct mutex3 *mutex);
    //@ requires mutex3(mutex) &*& mutex3_held(mutex);
    //@ ensures true;



#endif
