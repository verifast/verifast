#include "yahalom.h"

#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>

//@ import_module cryptolib;

struct yahalom_args
{
  int attacker;
  struct keypair *keypair;
  
  char sender;
  char receiver;
  struct item *key_AS;
  struct item *key_BS;
  struct item *key_AB;
};

/*@
predicate_family_instance pthread_run_pre(attacker_t)(void *data, any info) =
    exists(yahalom_pub) &*& [_]world(yahalom_pub) &*&
    yahalom_args_attacker(data, ?attacker) &*&
    true == bad(attacker) &*&
    generated_values(attacker, _) &*&
    yahalom_args_keypair(data, ?keypair) &*&    
    keypair(keypair, attacker, _, ?i, yahalom_pub) &*&
    principals_created(_) &*& info == nil;
@*/

void *attacker_t(void* data) //@ : pthread_run_joinable
  //@ requires pthread_run_pre(attacker_t)(data, ?info);
  //@ ensures false;
{
  //@ open pthread_run_pre(attacker_t)(data, info);
  struct yahalom_args *args = (void*) data;
  attacker(args->attacker, args->keypair);
  return 0;
}

/*@
predicate_family_instance pthread_run_pre(server_t)(void *data, any info) =
  [_]world(yahalom_pub) &*&
  yahalom_args_sender(data, ?sender) &*&
  yahalom_args_receiver(data, ?receiver) &*&
  yahalom_args_key_AS(data, ?key_AS) &*&
  yahalom_args_key_BS(data, ?key_BS) &*&
  yahalom_args_key_AB(data, ?key_AB) &*&
  !bad(server_id()) &*& !bad(sender) &*& !bad(receiver) &*&
  generated_values(server_id(), ?count) &*&
  item(key_AS, ?kas, yahalom_pub) &*& [_]info_for_item(kas, ?i_kas) &*&
    kas == symmetric_key_item(sender, 2) &*& i_kas == int_pair(2, 0) &*&
  item(key_BS, ?kbs, yahalom_pub) &*& [_]info_for_item(kbs, ?i_kbs) &*&
    kbs == symmetric_key_item(receiver, _) &*& i_kbs == int_pair(2, 0) &*&
  item(key_AB, ?kab, yahalom_pub) &*& [_]info_for_item(kab, ?i_kab) &*&
    kab == symmetric_key_item(server_id(), _) &*&
    i_kab == int_pair(3, int_pair(sender, receiver)) &*&
  info == nil;
predicate_family_instance pthread_run_post(server_t)(void *data, any info) =
  [_]world(yahalom_pub) &*&
  yahalom_args_sender(data, ?sender) &*&
  yahalom_args_receiver(data, ?receiver) &*&
  yahalom_args_key_AS(data, ?key_AS) &*&
  yahalom_args_key_BS(data, ?key_BS) &*&
  yahalom_args_key_AB(data, ?key_AB) &*&
  generated_values(server_id(), ?count) &*&
  info == nil;
@*/

void *server_t(void* data) //@ : pthread_run_joinable
  //@ requires pthread_run_pre(server_t)(data, ?x);
  //@ ensures pthread_run_post(server_t)(data, x) &*& result == 0;
{
  struct yahalom_args *args = data;
  //@ open pthread_run_pre(server_t)(data, _);
  server(args->sender, args->receiver, args->key_AS, args->key_BS, args->key_AB);
  /*@ if (!collision_in_run)
      {
        assert yahalom_args_key_AS(data, ?key_AS);
        assert yahalom_args_key_BS(data, ?key_BS);
        assert yahalom_args_key_AB(data, ?key_AB);
        assert item(key_AS, ?kas, yahalom_pub);
        assert item(key_BS, ?kbs, yahalom_pub);
        assert item(key_AB, ?kab, yahalom_pub);
        leak is_not_public(_, yahalom_pub, kas, _);
        leak is_not_public(_, yahalom_pub, kbs, _);
        leak is_not_public(_, yahalom_pub, kab, _);
      }
  @*/
  item_free(args->key_AS);
  item_free(args->key_BS);
  item_free(args->key_AB);
  //@ close pthread_run_post(server_t)(data, _);

  return 0;
}

/*@
predicate_family_instance pthread_run_pre(receiver_t)(void *data, any info) =
  [_]world(yahalom_pub) &*&
  yahalom_args_receiver(data, ?receiver) &*&
  yahalom_args_key_BS(data, ?key_BS) &*&
  !bad(server_id()) &*& !bad(receiver) &*&
  generated_values(receiver, _) &*&
  item(key_BS, ?kbs, yahalom_pub) &*& [_]info_for_item(kbs, ?i_kbs) &*&
    kbs == symmetric_key_item(receiver, _) &*& i_kbs == int_pair(2, 0) &*&
  info == cons(receiver, nil);
predicate_family_instance pthread_run_post(receiver_t)(void *data, any info) =
  [_]world(yahalom_pub) &*&
  yahalom_args_receiver(data, ?receiver) &*&
  yahalom_args_key_BS(data, ?key_BS) &*&
  generated_values(receiver, _) &*&
  info == cons(receiver, nil);
@*/

void *receiver_t(void* data) //@ : pthread_run_joinable
  //@ requires pthread_run_pre(receiver_t)(data, ?x);
  //@ ensures pthread_run_post(receiver_t)(data, x) &*& result == 0;
{
  struct yahalom_args *args = data;
  //@ open pthread_run_pre(receiver_t)(data, _);
  receiver(args->receiver, args->key_BS);
  item_free(args->key_BS);
  //@ close pthread_run_post(receiver_t)(data, _);
  return 0;
}

/*@
predicate_family_instance pthread_run_pre(sender_t)(void *data, any info) =
  [_]world(yahalom_pub) &*&
  yahalom_args_sender(data, ?sender) &*&
  yahalom_args_receiver(data, ?receiver) &*&
  yahalom_args_key_AS(data, ?key_AS) &*&
  !bad(server_id()) &*& !bad(sender) &*& !bad(receiver) &*&
  generated_values(sender, _) &*&
  item(key_AS, ?kas, yahalom_pub) &*& [_]info_for_item(kas, ?i_kas) &*&
    kas == symmetric_key_item(sender, _) &*& i_kas == int_pair(2, 0) &*&
  info == cons(sender, nil);
predicate_family_instance pthread_run_post(sender_t)(void *data, any info) =
  [_]world(yahalom_pub) &*&
  yahalom_args_sender(data, ?sender) &*&
  yahalom_args_receiver(data, ?receiver) &*&
  yahalom_args_key_AS(data, ?key_AS) &*&
  generated_values(sender, _) &*&
  info == cons(sender, nil);
@*/

void *sender_t(void* data) //@ : pthread_run_joinable
  //@ requires pthread_run_pre(sender_t)(data, ?x);
  //@ ensures pthread_run_post(sender_t)(data, x) &*& result == 0;
{
  struct yahalom_args *args = data;
  //@ open pthread_run_pre(sender_t)(data, _);
  struct item *result = sender(args->sender, args->receiver, args->key_AS);
  /*@ if (!collision_in_run)
      {
        assert yahalom_args_key_AS(data, ?key_AS);
        assert item(key_AS, ?kas, yahalom_pub);
        assert item(result, ?kab, yahalom_pub);
        leak is_not_public(_, yahalom_pub, kas, _);
        leak is_not_public(_, yahalom_pub, kab, _);
      }
  @*/
  item_free(result);
  item_free(args->key_AS);
  //@ close pthread_run_post(sender_t)(data, _);
  return 0;
}

int main() //@ : main_full(main_app)
  //@ requires module(main_app, true);
  //@ ensures  true;
{
  struct keypair* apair;
  struct keypair* server_pair;
  struct keypair* sender_pair;
  struct keypair* receiver_pair;
  struct item *key_AS;
  struct item *key_BS;
  struct item *key_AB;

  printf("\n\tExecuting \"yahalom protocol\" ... \n\n");
  //@ open_module();
  //@ PACK_PROOF_OBLIGATIONS(yahalom)
  init_crypto_lib();

  int attacker = create_principal(&apair);
  //@ assume (bad(attacker));
  int server_ = create_principal(&server_pair);
  keypair_free(server_pair);
  char server = (char) server_;
  int sender_ = create_principal(&sender_pair);
  keypair_free(sender_pair);
  char sender = (char) sender_;
  int receiver_ = create_principal(&receiver_pair);
  keypair_free(receiver_pair);
  char receiver = (char) receiver_;
  //@ leak  world(yahalom_pub);
  //@ close key_request(sender, int_pair(2, 0));
  key_AS = create_symmetric_key();
  //@ close key_request(receiver, int_pair(2, 0));
  key_BS = create_symmetric_key();
  //@ close key_request(server, int_pair(3, int_pair(sender, receiver)));
  key_AB = create_symmetric_key();
  //@ assert server == server_id();
  
  //@ assume (!bad(server) && !bad(sender) && !bad(receiver));
  void *null = (void *) 0;

  { 
    pthread_t a_thread;
    struct yahalom_args *args = malloc(sizeof(struct yahalom_args));
    if (args == 0) abort();
    args->attacker = attacker;
    args->keypair = apair;  
    //@ close pthread_run_pre(attacker_t)(args, _);
    pthread_create(&a_thread, NULL, &attacker_t, args);
  }

  int i = 0;
#ifdef EXECUTE
  while (i++ < 10)
#else
  while (true)
#endif
    /*@ invariant
              [_]world(yahalom_pub) &*&
              !bad(server) && !bad(sender) && !bad(receiver) &*&
              generated_values(sender, _) &*&
              item(key_AS, ?kkey_AS, yahalom_pub) &*& 
                kkey_AS == symmetric_key_item(sender, 2) &*&
                [_]info_for_item(kkey_AS, ?i_kkey_AS) &*&
                i_kkey_AS == int_pair(2, 0) &*&
              generated_values(receiver, _) &*&
              item(key_BS, ?kkey_BS, yahalom_pub) &*& 
                kkey_BS == symmetric_key_item(receiver, 2) &*&
                [_]info_for_item(kkey_BS, ?i_kkey_BS) &*&
                i_kkey_BS == int_pair(2, 0) &*&
              generated_values(server, _) &*&
              item(key_AB, ?kkey_AB, yahalom_pub) &*& 
                kkey_AB == symmetric_key_item(server, 2) &*&
                [_]info_for_item(kkey_AB, ?i_kkey_AB) &*&
                i_kkey_AB == int_pair(3, int_pair(sender, receiver));
    @*/
  {
    pthread_t serv_thread, send_thread, rec_thread;
    struct yahalom_args serv_args, send_args, rec_args;
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
