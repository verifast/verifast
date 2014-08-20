#include "secure_storage.h"

#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>

//@ import_module cryptolib;

/*@
predicate_family_instance pthread_run_pre(attacker_t)(void *data, any info) =
    exists(ss_pub) &*& [_]world(ss_pub) &*&
    attacker_proof_obligations(ss_pub) &*&
    principals_created(_) &*& info == nil;
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
  [_]world(ss_pub) &*&
  item(data, key_item(?sender, _, symmetric_key, int_pair(0, 0))) &*&
  info == cons(sender, nil);
predicate_family_instance pthread_run_post(receiver_t)(void *data, any info) =
  item(data, key_item(?sender, _, symmetric_key, int_pair(0, 0))) &*&
  info == cons(sender, nil);
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
  [_]world(ss_pub) &*& generated_values(?principal, ?count) &*&
  item(data, key_item(?sender, _, symmetric_key, int_pair(0, 0))) &*&
  info == cons(sender, nil);
predicate_family_instance pthread_run_post(sender_t)(void *data, any info) =
  generated_values(?principal, ?count) &*&
  item(data, key_item(?sender, _, symmetric_key, int_pair(0, 0))) &*&
  info == cons(sender, nil);
@*/

void *sender_t(void* data) //@ : pthread_run_joinable
  //@ requires pthread_run_pre(sender_t)(data, ?x);
  //@ ensures pthread_run_post(sender_t)(data, x) &*& result == 0;
{
  //@ open pthread_run_pre(sender_t)(data, _);
  struct item *key = data;
  int i = random_int();
  struct item *message = create_data_item(i);
  //@ assert item(data, key_item(?sender, _, _, _));
  //@ assume (app_send_event(sender, data_item(i)));
  app_send(key, message);
  //@ close pthread_run_post(sender_t)(data, _);
  item_free(message);
  return 0;
}

int main() //@ : main_full(main_app)
  //@ requires module(main_app, true);
  //@ ensures  true;
{
  struct item *key;
  struct item *s_key;
  struct item *r_key;

  printf("\n\tExecuting \"secure_storage protocol\" ... \n\n");
  //@ open_module();
  //@ close exists(ss_pub);
  init_crypto_lib();

  //@ open initial_principals();
  int sender = create_principal();
  //@ close key_request(sender, int_pair(0, 0));
  s_key = create_symmetric_key();
  r_key = item_clone(s_key);

  void *null = (void *) 0;

  {
    pthread_t a_thread;
    //@ leak  world(ss_pub);
    //@ PACK_ATTACKER_PROOF_OBLIGATIONS(ss)
    //@ close attacker_proof_obligations(ss_pub);
    //@ close pthread_run_pre(attacker_t)(null, _);
    pthread_create(&a_thread, null, &attacker_t, null);
  }

  int i = 0;
#ifdef EXECUTE
  while (i++ < 10)
#else
  while (true)
#endif
    /*@ invariant [_]world(ss_pub) &*& generated_values(_, _) &*&
          item(s_key, key_item(sender, _, symmetric_key, int_pair(0, 0))) &*&
          item(r_key, key_item(sender, _, symmetric_key, int_pair(0, 0)));
    @*/
  {
    pthread_t s_thread, r_thread;
    {
      //@ close pthread_run_pre(sender_t)(s_key, cons(sender, nil));
      pthread_create(&s_thread, null, &sender_t, s_key);
      //@ close pthread_run_pre(receiver_t)(r_key, cons(sender, nil));
      pthread_create(&r_thread, null, &receiver_t, r_key);
    }

    {
      pthread_join(r_thread, null);
      //@ open pthread_run_post(receiver_t)(r_key, _);
      pthread_join(s_thread, null);
      //@ open pthread_run_post(sender_t)(s_key, _);
    }
  }

  //@ close_module();
  //@ leak module(main_app, _);
  printf("Done\n");
}
