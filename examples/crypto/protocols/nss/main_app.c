#include "nss.h"

#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>

//@ import_module cryptolib;

/*@
predicate_family_instance pthread_run_pre(attacker_t)(void *data, any info) =
    exists(nss_pub) &*& [_]world(nss_pub) &*&
    attacker_proof_obligations(nss_pub) &*&
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

struct nss_args
{
  int sender;
  int receiver;
  struct item *key_AS;
  struct item *key_BS;
  struct item *key_AB;
};

/*@
predicate_family_instance pthread_run_pre(server_t)(void *data, any info) =
  [_]world(nss_pub) &*&
  nss_args_sender(data, ?sender) &*&
  nss_args_receiver(data, ?receiver) &*&
  nss_args_key_AS(data, ?key_AS) &*&
  nss_args_key_BS(data, ?key_BS) &*&
  nss_args_key_AB(data, ?key_AB) &*&
  !bad(server_id()) &*& !bad(sender) &*& !bad(receiver) &*&
  generated_values(server_id(), ?count1) &*&
  item(key_AS, key_item(sender, 1, symmetric_key, int_pair(0, 0))) &*&
  item(key_BS, key_item(receiver, 1, symmetric_key, int_pair(0, 0))) &*&
  item(key_AB, key_item(server_id(), ?id, symmetric_key, 
                        int_pair(2, int_pair(sender, receiver)))) &*&
  info == nil;
predicate_family_instance pthread_run_post(server_t)(void *data, any info) =
  [_]world(nss_pub) &*&
  nss_args_sender(data, ?sender) &*&
  nss_args_receiver(data, ?receiver) &*&
  nss_args_key_AS(data, ?key_AS) &*&
  nss_args_key_BS(data, ?key_BS) &*&
  nss_args_key_AB(data, ?key_AB) &*&
  generated_values(server_id(), ?count1) &*&
  info == nil;
@*/

void *server_t(void* data) //@ : pthread_run_joinable
  //@ requires pthread_run_pre(server_t)(data, ?x);
  //@ ensures pthread_run_post(server_t)(data, x) &*& result == 0;
{
  struct nss_args *args = data;
  //@ open pthread_run_pre(server_t)(data, _);
  server(args->sender, args->receiver, 
         args->key_AS, args->key_BS, args->key_AB);
  item_free(args->key_AS);
  item_free(args->key_BS);
  item_free(args->key_AB);
  //@ close pthread_run_post(server_t)(data, _);
  return 0;
}

/*@
predicate_family_instance pthread_run_pre(receiver_t)(void *data, any info) =
  [_]world(nss_pub) &*&
  nss_args_receiver(data, ?receiver) &*&
  nss_args_key_BS(data, ?key_BS) &*&
  !bad(server_id()) &*& !bad(receiver) &*&
  generated_values(receiver, _) &*&
  item(key_BS, key_item(receiver, 1, symmetric_key, int_pair(0, 0))) &*&
  info == cons(receiver, nil);
predicate_family_instance pthread_run_post(receiver_t)(void *data, any info) =
  [_]world(nss_pub) &*&
  nss_args_receiver(data, ?receiver) &*&
  nss_args_key_BS(data, ?key_BS) &*&
  generated_values(receiver, _) &*&
  info == cons(receiver, nil);
@*/

void *receiver_t(void* data) //@ : pthread_run_joinable
  //@ requires pthread_run_pre(receiver_t)(data, ?x);
  //@ ensures pthread_run_post(receiver_t)(data, x) &*& result == 0;
{
  struct nss_args *args = data;
  //@ open pthread_run_pre(receiver_t)(data, _);
  receiver(args->receiver, args->key_BS);
  item_free(args->key_BS);
  //@ close pthread_run_post(receiver_t)(data, _);
  return 0;
}

/*@
predicate_family_instance pthread_run_pre(sender_t)(void *data, any info) =
  [_]world(nss_pub) &*&
  nss_args_sender(data, ?sender) &*&
  nss_args_receiver(data, ?receiver) &*&
  nss_args_key_AS(data, ?key_AS) &*&
  !bad(server_id()) &*& !bad(sender) &*& !bad(receiver) &*&
  generated_values(sender, _) &*&
  item(key_AS, key_item(sender, 1, symmetric_key, int_pair(0, 0))) &*&
  info == cons(sender, nil);
predicate_family_instance pthread_run_post(sender_t)(void *data, any info) =
  [_]world(nss_pub) &*&
  nss_args_sender(data, ?sender) &*&
  nss_args_receiver(data, ?receiver) &*&
  nss_args_key_AS(data, ?key_AS) &*&
  generated_values(sender, _) &*&
  info == cons(sender, nil);
@*/

void *sender_t(void* data) //@ : pthread_run_joinable
  //@ requires pthread_run_pre(sender_t)(data, ?x);
  //@ ensures pthread_run_post(sender_t)(data, x) &*& result == 0;
{
  struct nss_args *args = data;
  //@ open pthread_run_pre(sender_t)(data, _);
  struct item *result = sender(args->sender, args->receiver, args->key_AS);
  item_free(result);
  item_free(args->key_AS);
  //@ close pthread_run_post(sender_t)(data, _);
  return 0;
}

int main() //@ : main_full(main_app)
  //@ requires module(main_app, true);
  //@ ensures  true;
{
  struct item *key_AS;
  struct item *key_BS;
  struct item *key_AB;

  printf("\n\tExecuting \"nss protocol\" ... \n\n");
  //@ open_module();
  //@ close exists(nss_pub);
  init_crypto_lib();

  //@ open initial_principals();
  int server = create_principal();
  //@ assert server == server_id();
  int sender = create_principal();
  int receiver = create_principal();
  //@ close key_request(sender, int_pair(0, 0));
  key_AS = create_symmetric_key();
  //@ close key_request(receiver, int_pair(0, 0));
  key_BS = create_symmetric_key();
  //@ close key_request(server_id(), int_pair(2, int_pair(sender, receiver)));
  key_AB = create_symmetric_key();
  
  //@ assume (!bad(server) && !bad(sender) && !bad(receiver));
  void *null = (void *) 0;

  {
    pthread_t a_thread;
    //@ PACK_ATTACKER_PROOF_OBLIGATIONS(nss)
    //@ close attacker_proof_obligations(nss_pub);
    //@ leak  world(nss_pub);
    //@ close pthread_run_pre(attacker_t)(null, _);
    pthread_create(&a_thread, null, &attacker_t, null);
  }

  int i = 0;
#ifdef EXECUTE
  while (i++ < 10)
#else
  while (true)
#endif
    /*@ invariant
              [_]world(nss_pub) &*&
              generated_values(sender, _) &*&
              item(key_AS, ?kas) &*& 
                kas == key_item(sender, 1, symmetric_key, int_pair(0, 0)) &*&
              generated_values(receiver, _) &*&
              item(key_BS, ?kbs) &*& 
                kbs == key_item(receiver, 1, symmetric_key, int_pair(0, 0)) &*&
              generated_values(server_id(), _) &*&
              item(key_AB, ?kab) &*&
                kab == key_item(server_id(), _, symmetric_key, 
                                int_pair(2, int_pair(sender, receiver)));
    @*/
  {
    pthread_t serv_thread, send_thread, rec_thread;
    struct nss_args serv_args, send_args, rec_args;
    {
      serv_args.sender = sender;
      serv_args.receiver = receiver;
      serv_args.key_AS = item_clone(key_AS);
      serv_args.key_BS = item_clone(key_BS);
      serv_args.key_AB = item_clone(key_AB);
      //@ close pthread_run_pre(server_t)(&serv_args, _);
      pthread_create(&serv_thread, null, &server_t, &serv_args);

      rec_args.receiver = receiver;
      rec_args.key_BS = item_clone(key_BS);
      //@ close pthread_run_pre(receiver_t)(&rec_args, cons(receiver, nil));
      pthread_create(&rec_thread, null, &receiver_t, &rec_args);

      send_args.sender = sender;
      send_args.receiver = receiver;
      send_args.key_AS = item_clone(key_AS);
      //@ close pthread_run_pre(sender_t)(&send_args, cons(sender, nil));
      pthread_create(&send_thread, null, &sender_t, &send_args);
    }

    {
      pthread_join(serv_thread, null);
      //@ open pthread_run_post(server_t)(&serv_args, _);
      pthread_join(rec_thread, null);
      //@ open pthread_run_post(receiver_t)(&rec_args, _);
      pthread_join(send_thread, null);
      //@ open pthread_run_post(sender_t)(&send_args, _);
    }
  }

  //@ close_module();
  //@ leak module(main_app, _);
  printf("Done\n");
}
