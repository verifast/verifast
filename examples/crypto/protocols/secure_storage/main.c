#include "secure_storage.h"
#include "attacker.h"

#include <pthread.h>
#include <stdio.h>

/*@
predicate_family_instance pthread_run_pre(attacker_t)(void *data, any info) = 
    exists(ss_pub) &*& [_]world(ss_pub) &*& [_]net_api_initialized() &*&
    attacker_proof_obligations(ss_pub) &*& initial_principals() &*& 
    !bad(0) &*& info == nil;
@*/

void *attacker_t(void* _unused) //@ : pthread_run_joinable
  //@ requires pthread_run_pre(attacker_t)(_unused, _);
  //@ ensures false;
{
  //@ open pthread_run_pre(attacker_t)(_unused, _);
  attacker();
  return 0;
}

/*@
predicate_family_instance pthread_run_pre(receiver_t)(void *data, any info) = 
  [_]world(ss_pub) &*& [_]net_api_initialized() &*&
  key_item(data, _, _, symmetric_key, int_pair(0, 0)) &*&
  info == nil;
predicate_family_instance pthread_run_post(receiver_t)(void *data, any info) =
  key_item(data, _, _, symmetric_key, int_pair(0, 0)) &*&
  info == nil;
@*/

void *receiver_t(void* data) //@ : pthread_run_joinable
  //@ requires pthread_run_pre(receiver_t)(data, ?x);
  //@ ensures pthread_run_post(receiver_t)(data, x) &*& result == 0;
{
  //@ open pthread_run_pre(receiver_t)(data, _);
  struct item *key = data;
  struct item *i = app_receive(key);
  item_free(i);
  //@ close pthread_run_post(receiver_t)(data, _);
  return 0;
}

/*@
predicate_family_instance pthread_run_pre(sender_t)(void *data, any info) = 
  [_]world(ss_pub) &*& [_]net_api_initialized() &*&
  key_item(data, ?sender, _, symmetric_key, int_pair(0, 0)) &*&
  info == cons(sender, nil);
predicate_family_instance pthread_run_post(sender_t)(void *data, any info) =
  key_item(data, ?sender, _, symmetric_key, int_pair(0, 0)) &*&
  info == cons(sender, nil);
@*/

void *sender_t(void* data) //@ : pthread_run_joinable
  //@ requires pthread_run_pre(sender_t)(data, ?x);
  //@ ensures pthread_run_post(sender_t)(data, x) &*& result == 0;
{
  //@ open pthread_run_pre(sender_t)(data, _);
  struct item *key = data;
  int i = choose();
  struct item *message = create_data_item(i);
  //@ assert key_item(data, ?sender, _, _, _);
  //@ assume (app_send_event(sender, data_item(i)));
  app_send(key, message);
  //@ close pthread_run_post(sender_t)(data, _);
  item_free(message);
  return 0;
}

int main() //@ : main
  //@ requires true;
  //@ ensures true;
{ 
  struct item *key; 
  struct item *s_key;
  struct item *r_key;
  struct keypair *keypair;
  
  printf("\n\tExecuting \"secure_storage protocol\" ... ");
  //@ close exists(ss_pub);
  init_crypto_lib();
  //@ init_protocol();

  //@ open initial_principals();
  int sender = create_principal(&key, &keypair);
  keypair_free(keypair);
  s_key = key_clone(key);
  r_key = key_clone(key);
  key_free(key);
  //@ close initial_principals();
  
  void *null = (void *) 0;
  
  {
    pthread_t a_thread;
    //@ PACK_ATTACKER_PROOF_OBLIGATIONS(ss)
    //@ close attacker_proof_obligations(ss_pub);
    //@ leak  world(ss_pub) &*& net_api_initialized();
    //@ close pthread_run_pre(attacker_t)(null, _);
    pthread_create(&a_thread, null, &attacker_t, null);  
  }
  
  int i = 0;
#ifdef EXECUTE
  while (i++ < 10)
#else
  while (true)
#endif
    /*@ invariant [_]world(ss_pub) &*& [_]net_api_initialized() &*&
                  key_item(s_key, sender, _, symmetric_key, int_pair(0, 0)) &*&
                  key_item(r_key, _, _, symmetric_key, int_pair(0, 0));
    @*/
  { 
    pthread_t s_thread, r_thread;
    {
      //@ close pthread_run_pre(receiver_t)(r_key, _);
      pthread_create(&r_thread, null, &receiver_t, r_key);
      //@ close pthread_run_pre(sender_t)(s_key, cons(sender, nil));
      pthread_create(&s_thread, null, &sender_t, s_key);
    }
    
    {
      pthread_join(r_thread, null);
      //@ open pthread_run_post(receiver_t)(r_key, _);
      pthread_join(s_thread, null);
      //@ open pthread_run_post(sender_t)(s_key, _);
    }
  }
  
  printf("Done\n");
}
