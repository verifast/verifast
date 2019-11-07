
#include <stdlib.h>
#include <unistd.h>
#include <pthread.h>
#include <bits/pthreadtypes.h>


static int g;
pthread_spinlock_t g_lock;

/*@

predicate g_pred() =
 integer(&g, ?vf_g)
 &*& vf_g >= 0 &*& vf_g <= 1024;

  @*/

/*@

predicate threadfn_info (int *g_l) = true;

inductive quad = quad(int a, int *b, int c, int d);

predicate_family_instance pthread_run_pre(threadfn)
 (void *data, any info) =
     [1/4]integer(&g_lock, ?lockid)
 &*& [1/4]pthread_spinlock(&g_lock, lockid, g_pred)
 &*& info == quad(lockid, &g_lock, lockid, 0)
 &*& true;

predicate_family_instance pthread_run_post(threadfn)
 (void *data, any info) =
     threadfn_info (?g_l)
 &*& [1/4]integer(&g_lock, ?lockid)
 &*& [1/4]pthread_spinlock(&g_lock, lockid, g_pred)
 &*& info == quad(lockid, &g_lock, lockid, 0)
 &*& true;

  @*/

void *threadfn(void* _unused) //@ : pthread_run_joinable
/*@ requires
        pthread_run_pre(threadfn)(_unused, ?x)
    &*& lockset(currentThread, nil);
  @*/
/*@ ensures
        pthread_run_post(threadfn)(_unused, x)
    &*& lockset(currentThread, nil)
    &*& result == 0;
  @*/
 {
//@ open pthread_run_pre(threadfn)(_unused,  x);
//@ close threadfn_info (&g_lock);
  pthread_spin_lock(&g_lock);
//@ assert pthread_spinlock_locked(_, ?locked_my_int, ?locked_g_pred, _, _);

//@ open g_pred();
  if (g < 1024) { g = g + 1; }
//@ close g_pred();

  pthread_spin_unlock(&g_lock);

//@ close pthread_run_post(threadfn)(_unused, x);
  return ((void *) 0);
 }

void run_instance(void)
/*@ requires
        integer(&g, ?vf_g0)
    &*& 0 <= vf_g0 &*& vf_g0 <= 1024
    &*& integer(&g_lock, _)
    &*& lockset(currentThread, nil)
    &*& true;
  @*/
/*@ ensures
        integer(&g, _)
    &*& integer(&g_lock, _)
    &*& lockset(currentThread, nil)
    &*& true;
  @*/
 {
  void *data = (void *) 0;
  pthread_t pthr1, pthr2;

  g = 41;
//@ assert integer(&g, ?vf_g1);

//@ close g_pred();
//@ close create_lock_ghost_args(g_pred, nil, nil);
  pthread_spin_init(&g_lock, 0);

//@ close pthread_run_pre(threadfn)(data, _);
  pthread_create(&pthr2, (void *) 0, &threadfn, data);
//@ close pthread_run_pre(threadfn)(data, _);
  pthread_create(&pthr1, (void *) 0, &threadfn, data);

  sleep(600);
  pthread_spin_lock(&g_lock);
//@ open g_pred();
  g = 55;
//@ close g_pred();
  pthread_spin_unlock(&g_lock);
  sleep(600);
//@ assert [1/2]pthread_spinlock(?my_g_lock, ?my_lockid, g_pred);

  pthread_join(pthr2, (void *) 0);
//@ open pthread_run_post(threadfn)(?thr2_data, quad(my_lockid, &g_lock, g_lock, 0));

  pthread_join(pthr1, (void *) 0);
//@ open pthread_run_post(threadfn)(?thr1_data, quad(my_lockid, &g_lock, g_lock, 0));

  pthread_spin_destroy(&g_lock);
//@ open g_pred();
//@ assert integer(&g, ?vf_g3);
//@ assert 0 <= vf_g3 && vf_g3 <= 1024;

  exit(0);
 }


int main (int argc, char** argv) //@ : custom_main_spec
/*@ requires
        module(pthreads, true) &*& lockset(currentThread, nil);
  @*/
/*@ ensures lockset(currentThread, nil);
  @*/
 {
//@ open_module();

  run_instance();

//@ close_module();
//@ leak module(pthreads, _);
  return (0);
 }

