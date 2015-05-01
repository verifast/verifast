#include "dummy_protocol.h"

#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>

//@ import_module cryptolib;

struct dummy_args
{
  int attacker;
  struct keypair *keypair;
};

/*@
predicate_family_instance pthread_run_pre(attacker_t)(void *data, any info) =
    exists(dummy_pub) &*& [_]world(dummy_pub) &*&
    dummy_args_attacker(data, ?attacker) &*&
    true == bad(attacker) &*&
    generated_values(attacker, _) &*&
    dummy_args_keypair(data, ?keypair) &*&    
    keypair(keypair, attacker, _, ?i, dummy_pub) &*&
    principals_created(_) &*& info == nil;
@*/

void *attacker_t(void* data) //@ : pthread_run_joinable
  //@ requires pthread_run_pre(attacker_t)(data, ?info);
  //@ ensures false;
{
  //@ open pthread_run_pre(attacker_t)(data, info);
  struct dummy_args *args = (void*) data;
  attacker(args->attacker, args->keypair);
  return 0;
}

/*@
predicate_family_instance pthread_run_pre(sender_t)(void *data, any info) =
  [_]world(dummy_pub);
predicate_family_instance pthread_run_post(sender_t)(void *data, any info) =
  true;
@*/

void *sender_t(void* data) //@ : pthread_run_joinable
  //@ requires pthread_run_pre(sender_t)(data, ?x);
  //@ ensures pthread_run_post(sender_t)(data, x) &*& result == 0;
{
  //@ open pthread_run_pre(sender_t)(data, x);
  send();
  //@ close pthread_run_post(sender_t)(data, x);
  return 0;
}

/*@
predicate_family_instance pthread_run_pre(receiver_t)(void *data, any info) =
  [_]world(dummy_pub);
predicate_family_instance pthread_run_post(receiver_t)(void *data, any info) =
  true;
@*/

void *receiver_t(void* data) //@ : pthread_run_joinable
  //@ requires pthread_run_pre(receiver_t)(data, ?x);
  //@ ensures pthread_run_post(receiver_t)(data, x) &*& result == 0;
{
  //@ open pthread_run_pre(receiver_t)(data, x);
  struct item *i = receive();
  item_free(i);
  //@ close pthread_run_post(receiver_t)(data, x);
  return 0;
}

int main() //@ : main_full(main_app)
  //@ requires module(main_app, true);
  //@ ensures  true;
{
  printf("\n\tExecuting \"");
  printf("dummy protocol");
  printf("\" ... \n\n");
  
  //@ open_module();
  //@ PACK_PROOF_OBLIGATIONS(dummy)
  init_crypto_lib();

  {
    struct keypair *apair;
    pthread_t a_thread;
    int attacker = create_principal(&apair);
    //@ assume (bad(attacker));
    struct dummy_args *args = malloc(sizeof(struct dummy_args));
    if (args == 0) abort();
    args->attacker = attacker;
    args->keypair = apair;  
    //@ leak world(dummy_pub);
    //@ close pthread_run_pre(attacker_t)(args, _);
    pthread_create(&a_thread, NULL, &attacker_t, args);
  }

  int i = 0;
#ifdef EXECUTE
  while (i++ < 10)
#else
  while (true)
#endif
    //@ invariant [_]world(dummy_pub);
  {
    pthread_t s_thread, r_thread;
    {
      //@ close pthread_run_pre(sender_t)(NULL, none);
      pthread_create(&s_thread, NULL, &sender_t, NULL);
      //@ close pthread_run_pre(receiver_t)(NULL, none);
      pthread_create(&r_thread, NULL, &receiver_t, NULL);
    }

    {
      pthread_join(r_thread, NULL);
      //@ open pthread_run_post(receiver_t)(NULL, _);
      pthread_join(s_thread, NULL);
      //@ open pthread_run_post(sender_t)(NULL, _);
    }
  }

  //@ close_module();
  //@ leak module(main_app, _);
  printf("Done\n");
}
