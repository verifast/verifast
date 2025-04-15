/*

Authors: Marko Doko and Viktor Vafeiadis, MPI-SWS; Bart Jacobs, KU Leuven

Based on:
- Viktor Vafeiadis and Chinmay Narayan. Relaxed separation logic: a program logic for C11 concurrency. OOPSLA 2013. http://www.mpi-sws.org/~viktor/papers/oopsla2013-rsl.pdf
- Marko Doko and Viktor Vafeiadis. A program logic for C11 memory fences. VMCAI 2016. http://www.mpi-sws.org/~viktor/papers/vmcai2016-fsl.pdf

*/

enum memory_order {
    memory_order_relaxed,
    memory_order_consume,
    memory_order_acquire,
    memory_order_release,
    memory_order_acq_rel,
    memory_order_seq_cst
};

//@ predicate Write(int *loc, predicate(int) Q);
//@ predicate Read(int *loc, predicate(int) Q);
//@ predicate RMW(int *loc, predicate(int) Q);
//@ predicate RelFenced(int threadId, predicate() P);
//@ predicate AcqFenced(int threadId, predicate() P);

//@ predicate_ctor apply(predicate(int) Q, int value)() = Q(value);
//@ predicate_ctor erased(predicate(int) Q, int value0)(int value) = value == value0 ? true : Q(value);

//@ predicate True() = true;
//@ predicate False() = false;
//@ predicate_ctor sep0(predicate() P1, predicate() P2)() = P1() &*& P2();
//@ predicate_ctor sep1(predicate(int) Q1, predicate(int) Q2)(int value) = Q1(value) &*& Q2(value);

/*@

fixpoint bool is_acquire(enum memory_order order) {
  return (order == memory_order_acquire) || (order == memory_order_acq_rel) || (order == memory_order_seq_cst);
} 

fixpoint bool is_release(enum memory_order order) {
  return (order == memory_order_release) || (order == memory_order_acq_rel) || (order == memory_order_seq_cst);
} 


// --- Initialization -----------------------------------

lemma void convert_to_atomic(int *loc, predicate(int) Q);
    requires *loc |-> ?value &*& Q(value);
    ensures Write(loc, Q) &*& Read(loc, Q);

lemma void convert_to_atomic_rmw(int *loc, predicate(int) Q);
    requires *loc |-> ?value &*& Q(value);
    ensures Write(loc, Q) &*& RMW(loc, Q);

@*/

// --- Atomic stores ------------------------------------

void atomic_store_explicit(int *loc, int value, enum memory_order order);
    //@ requires Write(loc, ?Q) &*& (is_release(order) ? Q(value) : RelFenced(currentThread, apply(Q,value)));
    //@ ensures Write(loc, Q);

void atomic_store_release(int *loc, int value);
    //@ requires Write(loc, ?Q) &*& Q(value);
    //@ ensures Write(loc, Q);

void atomic_store_relaxed(int *loc, int value);
    //@ requires Write(loc, ?Q) &*& RelFenced(currentThread, apply(Q,value));
    //@ ensures Write(loc, Q);

// --- Atomic loads -------------------------------------

/* The contract below would work, but would make the invariant in receiver()
below harder to state and/or prove, esp.  considering that in VeriFast
predicate extensionality is unsound.

int atomic_read_acquire(int *loc);
    //@ requires Read(loc, ?Q);
    //@ ensures Read(loc, erased(Q, result)) &*& Q(result);

*/

int atomic_load_explicit(int *loc, enum memory_order order);
    //@ requires exists<fixpoint(int, bool)>(?cond) &*& Read(loc, ?Q);
    //@ ensures cond(result) ? Read(loc, erased(Q, result)) &*& (is_acquire(order) ? Q(result) : AcqFenced(currentThread, apply(Q,result))) : Read(loc, Q);


int atomic_load_acquire(int *loc);
    //@ requires exists<fixpoint(int, bool)>(?cond) &*& Read(loc, ?Q);
    //@ ensures cond(result) ? Read(loc, erased(Q, result)) &*& Q(result) : Read(loc, Q);

int atomic_load_relaxed(int *loc);
    //@ requires exists<fixpoint(int, bool)>(?cond) &*& Read(loc, ?Q);
    //@ ensures cond(result) ? Read(loc, erased(Q, result)) &*& AcqFenced(currentThread, apply(Q,result)) : Read(loc, Q);


// --- Fences -------------------------------------------

void atomic_thread_fence(enum memory_order order);
    //@ requires exists<predicate()>(?P) &*& is_acquire(order) ? AcqFenced(currentThread, P) : P();
    //@ ensures is_release(order) ? RelFenced(currentThread, P) : P();

void fence_release();
    //@ requires exists<predicate()>(?P) &*& P();
    //@ ensures RelFenced(currentThread, P);

void fence_acquire();
    //@ requires AcqFenced(currentThread, ?P);
    //@ ensures P();


// --- Compare-exchange ---------------------------------

/*@

typedef lemma void CAS_premise(int exp_val, int new_val, predicate() P, predicate(int) Q, predicate() R)();
    requires P() &*& Q(exp_val);
    ensures Q(new_val) &*& R();

@*/

bool atomic_compare_exchange_acquire_release(int *loc, int exp_val, int new_val);
    //@ requires RMW(loc, ?Q) &*& is_CAS_premise(_, exp_val, new_val, ?P, Q, ?R) &*& P();
    //@ ensures RMW(loc, Q) &*& result ? R() : P();

/*@

// --- Administrative rules -----------------------------

lemma void dup_Write(int *loc);
    requires Write(loc, ?Q);
    ensures Write(loc, Q) &*& Write(loc, Q);

lemma void dup_RMW(int *loc);
    requires RMW(loc, ?Q);
    ensures RMW(loc, Q) &*& RMW(loc, Q);


lemma void split_Read(int *loc, predicate(int) Q1, predicate(int) Q2);
    requires Read(loc, sep1(Q1, Q2));
    ensures Read(loc, Q1) &*& Read(loc, Q2);

lemma void merge_Read(int *loc, predicate(int) Q1, predicate(int) Q2);
    requires Read(loc, Q1) &*& Read(loc, Q2);
    ensures Read(loc, sep1(Q1, Q2));

lemma void split_RelFenced(int *loc, predicate() P1, predicate() P2);
    requires RelFenced(?threadId, sep0(P1, P2));
    ensures RelFenced(threadId, P1) &*& RelFenced(threadId, P2);

lemma void merge_RelFenced(int *loc, predicate() P1, predicate() P2);
    requires RelFenced(?threadId, P1) &*& RelFenced(threadId, P2);
    ensures RelFenced(threadId, sep0(P1, P2));

lemma void RelFenced_True_intro(int threadId);
    requires true;
    ensures RelFenced(threadId, True);

lemma void RelFenced_elim();
    requires RelFenced(_, ?P);
    ensures P();

@*/

