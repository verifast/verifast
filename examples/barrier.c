#include "stdlib.h"
#include "threading.h"

// Inspired by [1].
// [1] Aquinas Hobor and Cristian Gherghina. Barriers in Concurrent Separation Logic. 2010.

// Verified general barriers implementation

struct barrier {
    struct mutex *mutex;
    int n;
    int k;
    bool outgoing;
};

/*@

predicate_ctor barrier_inv(struct barrier *barrier, int n, predicate(int k, bool outgoing) inv)() =
    barrier->k |-> ?k &*& barrier->outgoing |-> ?outgoing &*& inv(k, outgoing) &*&
    outgoing ? 1 <= k &*& k < n : 0 <= k &*& k < n;

predicate barrier(struct barrier *barrier, int n, predicate(int k, bool outgoing) inv;) =
    2 <= n &*& malloc_block_barrier(barrier) &*&
    barrier->mutex |-> ?mutex &*& barrier->n |-> n &*& mutex(mutex, barrier_inv(barrier, n, inv));

predicate create_barrier_ghost_arg(predicate(int k, bool outgoing) inv) = inv(0, false);

@*/

struct barrier *create_barrier(int n)
    //@ requires 2 <= n &*& create_barrier_ghost_arg(?inv);
    //@ ensures barrier(result, n, inv);
{
    //@ open create_barrier_ghost_arg(inv);
    struct barrier *barrier = malloc(sizeof(struct barrier));
    if (barrier == 0) abort();
    barrier->n = n;
    barrier->k = 0;
    barrier->outgoing = false;
    //@ close create_mutex_ghost_arg(barrier_inv(barrier, n, inv));
    //@ close barrier_inv(barrier, n, inv)();
    struct mutex *mutex = create_mutex();
    barrier->mutex = mutex;
    //@ close barrier(barrier, n, inv);
    return barrier;
}

/*@

predicate_family barrier_incoming(void *lem)(int n, predicate(int k, bool outgoing) inv, barrier_exit *exit);
predicate_family barrier_inside(void *lem)(int n, predicate(int k, bool outgoing) inv);
predicate_family barrier_exiting(void *lem)(int n, predicate(int k, bool outgoing) inv);

typedef lemma void barrier_enter(int k);
    requires barrier_incoming(this)(?n, ?inv, ?exit) &*& inv(k, false) &*& 0 <= k &*& k < n;
    ensures
        k == n - 1 ?
            barrier_exiting(exit)(n, inv) &*& inv(k, true)
        :
            barrier_inside(exit)(n, inv) &*& inv(k + 1, false);

typedef lemma void barrier_exit(int k);
    requires barrier_inside(this)(?n, ?inv) &*& inv(k, true) &*& 1 <= k &*& k < n;
    ensures barrier_exiting(this)(n, inv) &*& k == 1 ? inv(0, false) : inv(k - 1, true);

@*/

void barrier(struct barrier *barrier)
    /*@
    requires
        [?f]barrier(barrier, ?n, ?inv) &*&
        is_barrier_enter(?enter) &*& barrier_incoming(enter)(n, inv, ?exit) &*& is_barrier_exit(exit);
    @*/
    /*@
    ensures
        [f]barrier(barrier, n, inv) &*&
        barrier_exiting(exit)(n, inv);
    @*/
{
    //@ open barrier(barrier, n, inv);
    struct mutex *mutex = barrier->mutex;
    mutex_acquire(mutex);
    //@ open barrier_inv(barrier, n, inv)();
    {
        while (barrier->outgoing)
            /*@
            invariant
                mutex_held(mutex, barrier_inv(barrier, n, inv), currentThread, f) &*&
                barrier->k |-> ?k &*& barrier->outgoing |-> ?outgoing &*& inv(k, outgoing) &*&
                outgoing ? 1 <= k &*& k < n : 0 <= k &*& k < n;
            @*/
        {
            //@ close barrier_inv(barrier, n, inv)();
            mutex_release(mutex);
            mutex_acquire(mutex);
            //@ open barrier_inv(barrier, n, inv)();
        }
    }
    //@ enter(barrier->k);
    barrier->k++;
    if (barrier->k == barrier->n) {
        barrier->outgoing = true;
        barrier->k--;
        //@ close barrier_inv(barrier, n, inv)();
        mutex_release(barrier->mutex);
    } else {
        while (!barrier->outgoing)
            /*@
            invariant
                mutex_held(mutex, barrier_inv(barrier, n, inv), currentThread, f) &*&
                barrier->k |-> ?k &*& barrier->outgoing |-> ?outgoing &*& inv(k, outgoing) &*&
                outgoing ? 1 <= k &*& k < n : 0 <= k &*& k < n;
            @*/
        {
            //@ close barrier_inv(barrier, n, inv)();
            mutex_release(mutex);
            mutex_acquire(mutex);
            //@ open barrier_inv(barrier, n, inv)();
        }
        //@ exit(k);
        barrier->k--;
        if (barrier->k == 0) {
            barrier->outgoing = false;
        }
        //@ close barrier_inv(barrier, n, inv)();
        mutex_release(mutex);
    }
    //@ close [f]barrier(barrier, n, inv);
    //@ leak is_barrier_enter(_) &*& is_barrier_exit(_);
}

void barrier_dispose(struct barrier *barrier)
    //@ requires barrier(barrier, ?n, ?inv);
    //@ ensures inv(_, _);
{
    //@ open barrier(barrier, n, inv);
    mutex_dispose(barrier->mutex);
    //@ open barrier_inv(barrier, n, inv)();
    free(barrier);
}

// Example program

/*@

inductive phase = writing_x | writing_y;

fixpoint phase next_phase(phase p) {
    switch (p) {
        case writing_x: return writing_y;
        case writing_y: return writing_x;
    }
}

@*/

struct data {
    struct barrier *barrier;
    //@ phase phase;
    //@ phase phase1;
    //@ phase phase2;
    //@ bool inside1;
    //@ bool inside2;
    int x1;
    int x2;
    int y1;
    int y2;
    int i;
};

/*@

predicate_ctor my_barrier_inv(struct data *d)(int k, bool exiting) =
    d->phase |-> ?p &*&
    [1/2]d->inside1 |-> ?i1 &*&
    [1/2]d->inside2 |-> ?i2 &*&
    [1/2]d->phase1 |-> ?p1 &*& p == (exiting && i1 ? next_phase(p1) : p1) &*&
    [1/2]d->phase2 |-> ?p2 &*& p == (exiting && i2 ? next_phase(p2) : p2) &*&
    k == (i1 ? 1 : 0) + (i2 ? 1 : 0) &*&
    switch (p) {
        case writing_x: return
            (i1 ? [1/2]d->y1 |-> ?_ &*& [1/2]d->y2 |-> ?_ &*& d->x1 |-> ?_ &*& d->i |-> ?_ : emp) &*&
            (i2 ? [1/2]d->y1 |-> ?_ &*& [1/2]d->y2 |-> ?_ &*& d->x2 |-> ?_ : emp);
        case writing_y: return
            (i1 ? [1/2]d->x1 |-> ?_ &*& [1/2]d->x2 |-> ?_ &*& d->y1 |-> ?_ : emp) &*&
            (i2 ? [1/2]d->x1 |-> ?_ &*& [1/2]d->x2 |-> ?_ &*& d->y2 |-> ?_ &*& d->i |-> ?_ : emp);
    };

@*/

/*@

predicate_family_instance thread_run_pre(thread1)(struct data *d, any info) =
    [1/2]d->phase1 |-> writing_x &*& [1/2]d->inside1 |-> false &*& [1/2]d->y1 |-> ?_ &*& [1/2]d->y2 |-> ?_ &*& d->x1 |-> ?_ &*& d->i |-> ?_ &*&
    [1/3]d->barrier |-> ?barrier &*& [1/2]barrier(barrier, 2, my_barrier_inv(d));

predicate_family_instance thread_run_post(thread1)(struct data *d, any info) =
    [1/2]d->phase1 |-> writing_x &*& [1/2]d->inside1 |-> false &*& [1/2]d->y1 |-> ?_ &*& [1/2]d->y2 |-> ?_ &*& d->x1 |-> ?_ &*& d->i |-> 0 &*&
    [1/3]d->barrier |-> ?barrier &*& [1/2]barrier(barrier, 2, my_barrier_inv(d));

@*/

void thread1(struct data *d) //@ : thread_run_joinable
    //@ requires thread_run_pre(thread1)(d, ?info);
    //@ ensures thread_run_post(thread1)(d, info);
{
    //@ open thread_run_pre(thread1)(d, ?info_);
    struct barrier *barrier = d->barrier;
    {
        /*@
        predicate_family_instance barrier_incoming(enter)(int n, predicate(int k, bool outgoing) inv, barrier_exit *exit_) =
            n == 2 &*& inv == my_barrier_inv(d) &*& exit_ == bexit &*&
            [1/2]d->phase1 |-> writing_x &*& [1/2]d->inside1 |-> false &*&
            [1/2]d->y1 |-> ?_ &*& [1/2]d->y2 |-> ?_ &*& d->x1 |-> ?_ &*& d->i |-> ?_;
        predicate_family_instance barrier_inside(bexit)(int n, predicate(int k, bool outgoing) inv) =
            n == 2 &*& inv == my_barrier_inv(d) &*&
            [1/2]d->phase1 |-> writing_x &*& [1/2]d->inside1 |-> true;
        predicate_family_instance barrier_exiting(bexit)(int n, predicate(int k, bool outgoing) inv) =
            n == 2 &*& inv == my_barrier_inv(d) &*&
            [1/2]d->phase1 |-> writing_y &*& [1/2]d->inside1 |-> false &*&
            [1/2]d->x1 |-> ?_ &*& [1/2]d->x2 |-> ?_ &*& d->y1 |-> ?_;
        lemma void enter(int k) : barrier_enter
            requires barrier_incoming(enter)(?n, ?inv, ?exit_) &*& inv(k, false) &*& 0 <= k &*& k < n;
            ensures
                k == n - 1 ?
                    barrier_exiting(exit_)(n, inv) &*& inv(k, true)
                :
                    barrier_inside(exit_)(n, inv) &*& inv(k + 1, false);
        {
            open barrier_incoming(enter)(_, _, _);
            open my_barrier_inv(d)(k, false);
            if (k == n - 1) {
                d->phase = writing_y;
                d->phase1 = writing_y;
                close my_barrier_inv(d)(k, true);
                close barrier_exiting(bexit)(n, inv);
            } else {
                d->inside1 = true;
                close barrier_inside(bexit)(n, inv);
                close my_barrier_inv(d)(k + 1, false);
            }
        }
        lemma void bexit(int k) : barrier_exit
            requires barrier_inside(bexit)(?n, ?inv) &*& inv(k, true) &*& 1 <= k &*& k < n;
            ensures barrier_exiting(bexit)(n, inv) &*& k == 1 ? inv(0, false) : inv(k - 1, true);
        {
            open barrier_inside(bexit)(_, _);
            open my_barrier_inv(d)(k, true);
            d->inside1 = false;
            d->phase1 = writing_y;
            assert k == 1;
            close my_barrier_inv(d)(0, false);
            close barrier_exiting(bexit)(n, inv);
        }
        @*/
        //@ produce_lemma_function_pointer_chunk(enter);
        //@ produce_lemma_function_pointer_chunk(bexit);
        //@ close barrier_incoming(enter)(2, my_barrier_inv(d), bexit);
        barrier(barrier);
        //@ open barrier_exiting(bexit)(2, my_barrier_inv(d));
    }
    int N = 0;
    while (N < 30)
        /*@
        invariant
            [1/2]d->phase1 |-> writing_y &*& [1/2]d->inside1 |-> false &*& [1/2]d->x1 |-> ?_ &*& [1/2]d->x2 |-> ?_ &*& d->y1 |-> ?_ &*&
            [1/2]barrier(barrier, 2, my_barrier_inv(d));
        @*/
    {
        int a1 = d->x1;
        int a2 = d->x2;
        d->y1 = a1 + 2 * a2;
        {
            /*@
            predicate_family_instance barrier_incoming(enter)(int n, predicate(int k, bool outgoing) inv, barrier_exit *exit_) =
                n == 2 &*& inv == my_barrier_inv(d) &*& exit_ == bexit &*&
                [1/2]d->phase1 |-> writing_y &*& [1/2]d->inside1 |-> false &*&
                [1/2]d->x1 |-> ?_ &*& [1/2]d->x2 |-> ?_ &*& d->y1 |-> ?_;
            predicate_family_instance barrier_inside(bexit)(int n, predicate(int k, bool outgoing) inv) =
                n == 2 &*& inv == my_barrier_inv(d) &*&
                [1/2]d->phase1 |-> writing_y &*& [1/2]d->inside1 |-> true;
            predicate_family_instance barrier_exiting(bexit)(int n, predicate(int k, bool outgoing) inv) =
                n == 2 &*& inv == my_barrier_inv(d) &*&
                [1/2]d->phase1 |-> writing_x &*& [1/2]d->inside1 |-> false &*&
                [1/2]d->y1 |-> ?_ &*& [1/2]d->y2 |-> ?_ &*& d->x1 |-> ?_ &*& d->i |-> ?_;
            lemma void enter(int k) : barrier_enter
                requires barrier_incoming(enter)(?n, ?inv, ?exit_) &*& inv(k, false) &*& 0 <= k &*& k < n;
                ensures
                    k == n - 1 ?
                        barrier_exiting(exit_)(n, inv) &*& inv(k, true)
                    :
                        barrier_inside(exit_)(n, inv) &*& inv(k + 1, false);
            {
                open barrier_incoming(enter)(_, _, _);
                open my_barrier_inv(d)(k, false);
                if (k == n - 1) {
                    d->phase = writing_x;
                    d->phase1 = writing_x;
                    close my_barrier_inv(d)(k, true);
                    close barrier_exiting(bexit)(n, inv);
                } else {
                    d->inside1 = true;
                    close barrier_inside(bexit)(n, inv);
                    close my_barrier_inv(d)(k + 1, false);
                }
            }
            lemma void bexit(int k) : barrier_exit
                requires barrier_inside(bexit)(?n, ?inv) &*& inv(k, true) &*& 1 <= k &*& k < n;
                ensures barrier_exiting(bexit)(n, inv) &*& k == 1 ? inv(0, false) : inv(k - 1, true);
            {
                open barrier_inside(bexit)(_, _);
                open my_barrier_inv(d)(k, true);
                d->inside1 = false;
                d->phase1 = writing_x;
                assert k == 1;
                close my_barrier_inv(d)(0, false);
                close barrier_exiting(bexit)(n, inv);
            }
            @*/
            //@ produce_lemma_function_pointer_chunk(enter);
            //@ produce_lemma_function_pointer_chunk(bexit);
            //@ close barrier_incoming(enter)(2, my_barrier_inv(d), bexit);
            barrier(barrier);
            //@ open barrier_exiting(bexit)(2, my_barrier_inv(d));
        }
        a1 = d->y1;
        a2 = d->y2;
        d->x1 = a1 + 2 * a2;
        N = N + 1;
        d->i = N;
        {
            /*@
            predicate_family_instance barrier_incoming(enter)(int n, predicate(int k, bool outgoing) inv, barrier_exit *exit_) =
                n == 2 &*& inv == my_barrier_inv(d) &*& exit_ == bexit &*&
                [1/2]d->phase1 |-> writing_x &*& [1/2]d->inside1 |-> false &*&
                [1/2]d->y1 |-> ?_ &*& [1/2]d->y2 |-> ?_ &*& d->x1 |-> ?_ &*& d->i |-> ?_;
            predicate_family_instance barrier_inside(bexit)(int n, predicate(int k, bool outgoing) inv) =
                n == 2 &*& inv == my_barrier_inv(d) &*&
                [1/2]d->phase1 |-> writing_x &*& [1/2]d->inside1 |-> true;
            predicate_family_instance barrier_exiting(bexit)(int n, predicate(int k, bool outgoing) inv) =
                n == 2 &*& inv == my_barrier_inv(d) &*&
                [1/2]d->phase1 |-> writing_y &*& [1/2]d->inside1 |-> false &*&
                [1/2]d->x1 |-> ?_ &*& [1/2]d->x2 |-> ?_ &*& d->y1 |-> ?_;
            lemma void enter(int k) : barrier_enter
                requires barrier_incoming(enter)(?n, ?inv, ?exit_) &*& inv(k, false) &*& 0 <= k &*& k < n;
                ensures
                    k == n - 1 ?
                        barrier_exiting(exit_)(n, inv) &*& inv(k, true)
                    :
                        barrier_inside(exit_)(n, inv) &*& inv(k + 1, false);
            {
                open barrier_incoming(enter)(_, _, _);
                open my_barrier_inv(d)(k, false);
                if (k == n - 1) {
                    d->phase = writing_y;
                    d->phase1 = writing_y;
                    close my_barrier_inv(d)(k, true);
                    close barrier_exiting(bexit)(n, inv);
                } else {
                    d->inside1 = true;
                    close barrier_inside(bexit)(n, inv);
                    close my_barrier_inv(d)(k + 1, false);
                }
            }
            lemma void bexit(int k) : barrier_exit
                requires barrier_inside(bexit)(?n, ?inv) &*& inv(k, true) &*& 1 <= k &*& k < n;
                ensures barrier_exiting(bexit)(n, inv) &*& k == 1 ? inv(0, false) : inv(k - 1, true);
            {
                open barrier_inside(bexit)(_, _);
                open my_barrier_inv(d)(k, true);
                d->inside1 = false;
                d->phase1 = writing_y;
                assert k == 1;
                close my_barrier_inv(d)(0, false);
                close barrier_exiting(bexit)(n, inv);
            }
            @*/
            //@ produce_lemma_function_pointer_chunk(enter);
            //@ produce_lemma_function_pointer_chunk(bexit);
            //@ close barrier_incoming(enter)(2, my_barrier_inv(d), bexit);
            barrier(barrier);
            //@ open barrier_exiting(bexit)(2, my_barrier_inv(d));
        }
    }
    {
        /*@
        predicate_family_instance barrier_incoming(enter)(int n, predicate(int k, bool outgoing) inv, barrier_exit *exit_) =
            n == 2 &*& inv == my_barrier_inv(d) &*& exit_ == bexit &*&
            [1/2]d->phase1 |-> writing_y &*& [1/2]d->inside1 |-> false &*&
            [1/2]d->x1 |-> ?_ &*& [1/2]d->x2 |-> ?_ &*& d->y1 |-> ?_;
        predicate_family_instance barrier_inside(bexit)(int n, predicate(int k, bool outgoing) inv) =
            n == 2 &*& inv == my_barrier_inv(d) &*&
            [1/2]d->phase1 |-> writing_y &*& [1/2]d->inside1 |-> true;
        predicate_family_instance barrier_exiting(bexit)(int n, predicate(int k, bool outgoing) inv) =
            n == 2 &*& inv == my_barrier_inv(d) &*&
            [1/2]d->phase1 |-> writing_x &*& [1/2]d->inside1 |-> false &*&
            [1/2]d->y1 |-> ?_ &*& [1/2]d->y2 |-> ?_ &*& d->x1 |-> ?_ &*& d->i |-> ?_;
        lemma void enter(int k) : barrier_enter
            requires barrier_incoming(enter)(?n, ?inv, ?exit_) &*& inv(k, false) &*& 0 <= k &*& k < n;
            ensures
                k == n - 1 ?
                    barrier_exiting(exit_)(n, inv) &*& inv(k, true)
                :
                    barrier_inside(exit_)(n, inv) &*& inv(k + 1, false);
        {
            open barrier_incoming(enter)(_, _, _);
            open my_barrier_inv(d)(k, false);
            if (k == n - 1) {
                d->phase = writing_x;
                d->phase1 = writing_x;
                close my_barrier_inv(d)(k, true);
                close barrier_exiting(bexit)(n, inv);
            } else {
                d->inside1 = true;
                close barrier_inside(bexit)(n, inv);
                close my_barrier_inv(d)(k + 1, false);
            }
        }
        lemma void bexit(int k) : barrier_exit
            requires barrier_inside(bexit)(?n, ?inv) &*& inv(k, true) &*& 1 <= k &*& k < n;
            ensures barrier_exiting(bexit)(n, inv) &*& k == 1 ? inv(0, false) : inv(k - 1, true);
        {
            open barrier_inside(bexit)(_, _);
            open my_barrier_inv(d)(k, true);
            d->inside1 = false;
            d->phase1 = writing_x;
            assert k == 1;
            close my_barrier_inv(d)(0, false);
            close barrier_exiting(bexit)(n, inv);
        }
        @*/
        //@ produce_lemma_function_pointer_chunk(enter);
        //@ produce_lemma_function_pointer_chunk(bexit);
        //@ close barrier_incoming(enter)(2, my_barrier_inv(d), bexit);
        barrier(barrier);
        //@ open barrier_exiting(bexit)(2, my_barrier_inv(d));
    }
    d->i = 0;
    //@ close thread_run_post(thread1)(d, info_);
}

/*@

predicate_family_instance thread_run_pre(thread2)(struct data *d, any info) =
    [1/2]d->phase2 |-> writing_x &*& [1/2]d->inside2 |-> false &*& [1/2]d->y1 |-> ?_ &*& [1/2]d->y2 |-> ?_ &*& d->x2 |-> ?_ &*&
    [1/3]d->barrier |-> ?barrier &*& [1/2]barrier(barrier, 2, my_barrier_inv(d));

predicate_family_instance thread_run_post(thread2)(struct data *d, any info) =
    [1/2]d->phase2 |-> writing_x &*& [1/2]d->inside2 |-> false &*& [1/2]d->y1 |-> ?_ &*& [1/2]d->y2 |-> ?_ &*& d->x2 |-> ?_ &*&
    [1/3]d->barrier |-> ?barrier &*& [1/2]barrier(barrier, 2, my_barrier_inv(d));

@*/

void thread2(struct data *d) //@ : thread_run_joinable
    //@ requires thread_run_pre(thread2)(d, ?info);
    //@ ensures thread_run_post(thread2)(d, info);
{
    //@ open thread_run_pre(thread2)(d, ?info_);
    struct barrier *barrier = d->barrier;
    {
        /*@
        predicate_family_instance barrier_incoming(enter)(int n, predicate(int k, bool outgoing) inv, barrier_exit *exit_) =
            n == 2 &*& inv == my_barrier_inv(d) &*& exit_ == bexit &*&
            [1/2]d->phase2 |-> writing_x &*& [1/2]d->inside2 |-> false &*&
            [1/2]d->y1 |-> ?_ &*& [1/2]d->y2 |-> ?_ &*& d->x2 |-> ?_;
        predicate_family_instance barrier_inside(bexit)(int n, predicate(int k, bool outgoing) inv) =
            n == 2 &*& inv == my_barrier_inv(d) &*&
            [1/2]d->phase2 |-> writing_x &*& [1/2]d->inside2 |-> true;
        predicate_family_instance barrier_exiting(bexit)(int n, predicate(int k, bool outgoing) inv) =
            n == 2 &*& inv == my_barrier_inv(d) &*&
            [1/2]d->phase2 |-> writing_y &*& [1/2]d->inside2 |-> false &*&
            [1/2]d->x1 |-> ?_ &*& [1/2]d->x2 |-> ?_ &*& d->y2 |-> ?_ &*& d->i |-> ?_;
        lemma void enter(int k) : barrier_enter
            requires barrier_incoming(enter)(?n, ?inv, ?exit_) &*& inv(k, false) &*& 0 <= k &*& k < n;
            ensures
                k == n - 1 ?
                    barrier_exiting(exit_)(n, inv) &*& inv(k, true)
                :
                    barrier_inside(exit_)(n, inv) &*& inv(k + 1, false);
        {
            open barrier_incoming(enter)(_, _, _);
            open my_barrier_inv(d)(k, false);
            if (k == n - 1) {
                d->phase = writing_y;
                d->phase2 = writing_y;
                close my_barrier_inv(d)(k, true);
                close barrier_exiting(bexit)(n, inv);
            } else {
                d->inside2 = true;
                close barrier_inside(bexit)(n, inv);
                close my_barrier_inv(d)(k + 1, false);
            }
        }
        lemma void bexit(int k) : barrier_exit
            requires barrier_inside(bexit)(?n, ?inv) &*& inv(k, true) &*& 1 <= k &*& k < n;
            ensures barrier_exiting(bexit)(n, inv) &*& k == 1 ? inv(0, false) : inv(k - 1, true);
        {
            open barrier_inside(bexit)(_, _);
            open my_barrier_inv(d)(k, true);
            d->inside2 = false;
            d->phase2 = writing_y;
            assert k == 1;
            close my_barrier_inv(d)(0, false);
            close barrier_exiting(bexit)(n, inv);
        }
        @*/
        //@ produce_lemma_function_pointer_chunk(enter);
        //@ produce_lemma_function_pointer_chunk(bexit);
        //@ close barrier_incoming(enter)(2, my_barrier_inv(d), bexit);
        barrier(barrier);
        //@ open barrier_exiting(bexit)(2, my_barrier_inv(d));
    }
    int m = 0;
    while (m < 30)
        /*@
        invariant
            [1/2]d->phase2 |-> writing_y &*& [1/2]d->inside2 |-> false &*& [1/2]d->x1 |-> ?_ &*& [1/2]d->x2 |-> ?_ &*& d->y2 |-> ?_ &*&
            d->i |-> ?_ &*& [1/2]barrier(barrier, 2, my_barrier_inv(d));
        @*/
    {
        int a1 = d->x1;
        int a2 = d->x2;
        d->y2 = a1 + 3 * a2;
        {
            /*@
            predicate_family_instance barrier_incoming(enter)(int n, predicate(int k, bool outgoing) inv, barrier_exit *exit_) =
                n == 2 &*& inv == my_barrier_inv(d) &*& exit_ == bexit &*&
                [1/2]d->phase2 |-> writing_y &*& [1/2]d->inside2 |-> false &*&
                [1/2]d->x1 |-> ?_ &*& [1/2]d->x2 |-> ?_ &*& d->y2 |-> ?_ &*& d->i |-> ?_;
            predicate_family_instance barrier_inside(bexit)(int n, predicate(int k, bool outgoing) inv) =
                n == 2 &*& inv == my_barrier_inv(d) &*&
                [1/2]d->phase2 |-> writing_y &*& [1/2]d->inside2 |-> true;
            predicate_family_instance barrier_exiting(bexit)(int n, predicate(int k, bool outgoing) inv) =
                n == 2 &*& inv == my_barrier_inv(d) &*&
                [1/2]d->phase2 |-> writing_x &*& [1/2]d->inside2 |-> false &*&
                [1/2]d->y1 |-> ?_ &*& [1/2]d->y2 |-> ?_ &*& d->x2 |-> ?_;
            lemma void enter(int k) : barrier_enter
                requires barrier_incoming(enter)(?n, ?inv, ?exit_) &*& inv(k, false) &*& 0 <= k &*& k < n;
                ensures
                    k == n - 1 ?
                        barrier_exiting(exit_)(n, inv) &*& inv(k, true)
                    :
                        barrier_inside(exit_)(n, inv) &*& inv(k + 1, false);
            {
                open barrier_incoming(enter)(_, _, _);
                open my_barrier_inv(d)(k, false);
                if (k == n - 1) {
                    d->phase = writing_x;
                    d->phase2 = writing_x;
                    close my_barrier_inv(d)(k, true);
                    close barrier_exiting(bexit)(n, inv);
                } else {
                    d->inside2 = true;
                    close barrier_inside(bexit)(n, inv);
                    close my_barrier_inv(d)(k + 1, false);
                }
            }
            lemma void bexit(int k) : barrier_exit
                requires barrier_inside(bexit)(?n, ?inv) &*& inv(k, true) &*& 1 <= k &*& k < n;
                ensures barrier_exiting(bexit)(n, inv) &*& k == 1 ? inv(0, false) : inv(k - 1, true);
            {
                open barrier_inside(bexit)(_, _);
                open my_barrier_inv(d)(k, true);
                d->inside2 = false;
                d->phase2 = writing_x;
                assert k == 1;
                close my_barrier_inv(d)(0, false);
                close barrier_exiting(bexit)(n, inv);
            }
            @*/
            //@ produce_lemma_function_pointer_chunk(enter);
            //@ produce_lemma_function_pointer_chunk(bexit);
            //@ close barrier_incoming(enter)(2, my_barrier_inv(d), bexit);
            barrier(barrier);
            //@ open barrier_exiting(bexit)(2, my_barrier_inv(d));
        }
        a1 = d->y1;
        a2 = d->y2;
        d->x2 = a1 + 3 * a2;
        {
            /*@
            predicate_family_instance barrier_incoming(enter)(int n, predicate(int k, bool outgoing) inv, barrier_exit *exit_) =
                n == 2 &*& inv == my_barrier_inv(d) &*& exit_ == bexit &*&
                [1/2]d->phase2 |-> writing_x &*& [1/2]d->inside2 |-> false &*&
                [1/2]d->y1 |-> ?_ &*& [1/2]d->y2 |-> ?_ &*& d->x2 |-> ?_;
            predicate_family_instance barrier_inside(bexit)(int n, predicate(int k, bool outgoing) inv) =
                n == 2 &*& inv == my_barrier_inv(d) &*&
                [1/2]d->phase2 |-> writing_x &*& [1/2]d->inside2 |-> true;
            predicate_family_instance barrier_exiting(bexit)(int n, predicate(int k, bool outgoing) inv) =
                n == 2 &*& inv == my_barrier_inv(d) &*&
                [1/2]d->phase2 |-> writing_y &*& [1/2]d->inside2 |-> false &*&
                [1/2]d->x1 |-> ?_ &*& [1/2]d->x2 |-> ?_ &*& d->y2 |-> ?_ &*& d->i |-> ?_;
            lemma void enter(int k) : barrier_enter
                requires barrier_incoming(enter)(?n, ?inv, ?exit_) &*& inv(k, false) &*& 0 <= k &*& k < n;
                ensures
                    k == n - 1 ?
                        barrier_exiting(exit_)(n, inv) &*& inv(k, true)
                    :
                        barrier_inside(exit_)(n, inv) &*& inv(k + 1, false);
            {
                open barrier_incoming(enter)(_, _, _);
                open my_barrier_inv(d)(k, false);
                if (k == n - 1) {
                    d->phase = writing_y;
                    d->phase2 = writing_y;
                    close my_barrier_inv(d)(k, true);
                    close barrier_exiting(bexit)(n, inv);
                } else {
                    d->inside2 = true;
                    close barrier_inside(bexit)(n, inv);
                    close my_barrier_inv(d)(k + 1, false);
                }
            }
            lemma void bexit(int k) : barrier_exit
                requires barrier_inside(bexit)(?n, ?inv) &*& inv(k, true) &*& 1 <= k &*& k < n;
                ensures barrier_exiting(bexit)(n, inv) &*& k == 1 ? inv(0, false) : inv(k - 1, true);
            {
                open barrier_inside(bexit)(_, _);
                open my_barrier_inv(d)(k, true);
                d->inside2 = false;
                d->phase2 = writing_y;
                assert k == 1;
                close my_barrier_inv(d)(0, false);
                close barrier_exiting(bexit)(n, inv);
            }
            @*/
            //@ produce_lemma_function_pointer_chunk(enter);
            //@ produce_lemma_function_pointer_chunk(bexit);
            //@ close barrier_incoming(enter)(2, my_barrier_inv(d), bexit);
            barrier(barrier);
            //@ open barrier_exiting(bexit)(2, my_barrier_inv(d));
        }
        m = d->i;
    }
    {
        /*@
        predicate_family_instance barrier_incoming(enter)(int n, predicate(int k, bool outgoing) inv, barrier_exit *exit_) =
            n == 2 &*& inv == my_barrier_inv(d) &*& exit_ == bexit &*&
            [1/2]d->phase2 |-> writing_y &*& [1/2]d->inside2 |-> false &*&
            [1/2]d->x1 |-> ?_ &*& [1/2]d->x2 |-> ?_ &*& d->y2 |-> ?_ &*& d->i |-> ?_;
        predicate_family_instance barrier_inside(bexit)(int n, predicate(int k, bool outgoing) inv) =
            n == 2 &*& inv == my_barrier_inv(d) &*&
            [1/2]d->phase2 |-> writing_y &*& [1/2]d->inside2 |-> true;
        predicate_family_instance barrier_exiting(bexit)(int n, predicate(int k, bool outgoing) inv) =
            n == 2 &*& inv == my_barrier_inv(d) &*&
            [1/2]d->phase2 |-> writing_x &*& [1/2]d->inside2 |-> false &*&
            [1/2]d->y1 |-> ?_ &*& [1/2]d->y2 |-> ?_ &*& d->x2 |-> ?_;
        lemma void enter(int k) : barrier_enter
            requires barrier_incoming(enter)(?n, ?inv, ?exit_) &*& inv(k, false) &*& 0 <= k &*& k < n;
            ensures
                k == n - 1 ?
                    barrier_exiting(exit_)(n, inv) &*& inv(k, true)
                :
                    barrier_inside(exit_)(n, inv) &*& inv(k + 1, false);
        {
            open barrier_incoming(enter)(_, _, _);
            open my_barrier_inv(d)(k, false);
            if (k == n - 1) {
                d->phase = writing_x;
                d->phase2 = writing_x;
                close my_barrier_inv(d)(k, true);
                close barrier_exiting(bexit)(n, inv);
            } else {
                d->inside2 = true;
                close barrier_inside(bexit)(n, inv);
                close my_barrier_inv(d)(k + 1, false);
            }
        }
        lemma void bexit(int k) : barrier_exit
            requires barrier_inside(bexit)(?n, ?inv) &*& inv(k, true) &*& 1 <= k &*& k < n;
            ensures barrier_exiting(bexit)(n, inv) &*& k == 1 ? inv(0, false) : inv(k - 1, true);
        {
            open barrier_inside(bexit)(_, _);
            open my_barrier_inv(d)(k, true);
            d->inside2 = false;
            d->phase2 = writing_x;
            assert k == 1;
            close my_barrier_inv(d)(0, false);
            close barrier_exiting(bexit)(n, inv);
        }
        @*/
        //@ produce_lemma_function_pointer_chunk(enter);
        //@ produce_lemma_function_pointer_chunk(bexit);
        //@ close barrier_incoming(enter)(2, my_barrier_inv(d), bexit);
        barrier(barrier);
        //@ open barrier_exiting(bexit)(2, my_barrier_inv(d));
    }
    //@ close thread_run_post(thread2)(d, info_);
}

int main() //@ : main
    //@ requires true;
    //@ ensures true;
{
    struct data *d = calloc(1, sizeof(struct data));
    if (d == 0) abort();
    //@ d->inside1 = false;
    //@ d->inside2 = false;
    //@ d->phase = writing_x;
    //@ d->phase1 = writing_x;
    //@ d->phase2 = writing_x;
    //@ close my_barrier_inv(d)(0, false);
    //@ close create_barrier_ghost_arg(my_barrier_inv(d));
    struct barrier *barrier = create_barrier(2);
    d->barrier = barrier;
    //@ close thread_run_pre(thread1)(d, unit);
    struct thread *t1 = thread_start_joinable(thread1, d);
    //@ close thread_run_pre(thread2)(d, unit);
    struct thread *t2 = thread_start_joinable(thread2, d);
    thread_join(t1);
    //@ open thread_run_post(thread1)(_, _);
    thread_join(t2);
    //@ open thread_run_post(thread2)(_, _);
    barrier_dispose(d->barrier);
    //@ open my_barrier_inv(d)(_, _);
    free(d);
    return 0;
}
