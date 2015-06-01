#include "dummy.h"

#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>

//@ import_module public_invariant;

/*@
predicate dummy_proof_pred() = true;

predicate_family_instance pthread_run_pre(attacker_t)(void *data, any info) =
    [_]public_invar(dummy_pub) &*&
    public_invariant_constraints(dummy_pub, dummy_proof_pred) &*&
    principals(_);
@*/

void *attacker_t(void* data) //@ : pthread_run_joinable
  //@ requires pthread_run_pre(attacker_t)(data, ?info);
  //@ ensures  false;
{
  while(true)
    //@ invariant pthread_run_pre(attacker_t)(data, info);
  {
    //@ open pthread_run_pre(attacker_t)(data, info);
    //@ close dummy_proof_pred();
    attacker();
    //@ open dummy_proof_pred();
    //@ close pthread_run_pre(attacker_t)(data, info);
  }
   
  return 0;
}

/*@
predicate_family_instance pthread_run_pre(sender_t)(void *data, any info) = 
  true 
;

predicate_family_instance pthread_run_post(sender_t)(void *data, any info) = 
  true 
;
@*/

void *sender_t(void *data) //@ : pthread_run_joinable
  //@ requires pthread_run_pre(sender_t)(data, ?x);
  //@ ensures pthread_run_post(sender_t)(data, x) &*& result == 0;
{
  //@ open pthread_run_pre(sender_t)(data, _);
  sender();
  //@ close pthread_run_post(sender_t)(data, x);
  return 0;
}

/*@
predicate_family_instance pthread_run_pre(receiver_t)(void *data, any info) = 
  true 
;

predicate_family_instance pthread_run_post(receiver_t)(void *data, any info) = 
  true 
;
@*/

void *receiver_t(void* data) //@ : pthread_run_joinable
  //@ requires pthread_run_pre(receiver_t)(data, ?x);
  //@ ensures pthread_run_post(receiver_t)(data, x) &*& result == 0;
{
  //@ open pthread_run_pre(receiver_t)(data, _);
  receiver();
  //@ close pthread_run_post(receiver_t)(data, x);
  return 0;
}

int main(int argc, char **argv) //@ : main_full(main_app)
    //@ requires module(main_app, true);
    //@ ensures true;
{
  //@ open_module();
  //@ assert module(public_invariant, true);
  
  pthread_t a_thread;
  havege_state havege_state;
  
  printf("\n\tExecuting \"");
  printf("dummy protocol");
  printf("\" ... \n\n");
  
  //@ PUBLIC_INVARIANT_CONSTRAINTS(dummy)
  //@ public_invariant_init(dummy_pub);
  
  //@ principals_init();
  //@ int attacker = principal_create();
  //@ int client = principal_create();
  //@ int server = principal_create();
  
  //@ close havege_state(&havege_state);
  havege_init(&havege_state);
  //@ close pthread_run_pre(attacker_t)(NULL, nil);
  pthread_create(&a_thread, NULL, &attacker_t, NULL);
  
  int i = 0;
#ifdef EXECUTE
  while (i++ < 10)
#else
  while (true)
#endif
    /*@ invariant havege_state_initialized(&havege_state) &*&
                  generated_values(client, ?count_c) &*&
                  generated_values(server, ?count_s);
    @*/
  {
    char* key;
    char request[PACKAGE_SIZE];
    char response[PACKAGE_SIZE];
    int temp;
    int message_len;

    {
      pthread_t s_thread, c_thread;

      //@ close pthread_run_pre(sender_t)(NULL, nil);
      pthread_create(&s_thread, NULL, &sender_t, NULL);
      //@ close pthread_run_pre(receiver_t)(NULL, nil);
      pthread_create(&c_thread, NULL, &receiver_t, NULL);
      
      pthread_join(s_thread, NULL);
      //@ open pthread_run_post(sender_t)(NULL, nil);
      pthread_join(c_thread, NULL);
      //@ open pthread_run_post(receiver_t)(NULL, nil);
    }
  }
  
  printf("Done\n");
  return 0;
}

