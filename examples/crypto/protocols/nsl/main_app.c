#include "nsl.h"

#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>

//@ import_module cryptolib;

struct nsl_args
{
  int attacker;
  struct keypair *keypair;
  
  char sender;
  char receiver;
  char server;  
  struct item *key_A_priv;
  struct item *key_B_priv;
  struct item *key_S_pub;
  struct item *key_S_priv;
};

/*@
predicate_family_instance pthread_run_pre(attacker_t)(void *data, any info) =
    exists(nsl_pub) &*& [_]world(nsl_pub) &*&
    nsl_args_attacker(data, ?attacker) &*&
    true == bad(attacker) &*&
    generated_values(attacker, _) &*&
    nsl_args_keypair(data, ?keypair) &*&    
    keypair(keypair, attacker, _, ?i, nsl_pub) &*&
    principals_created(_) &*& info == nil;
@*/

void *attacker_t(void* data) //@ : pthread_run_joinable
  //@ requires pthread_run_pre(attacker_t)(data, ?info);
  //@ ensures false;
{
  //@ open pthread_run_pre(attacker_t)(data, info);
  struct nsl_args *args = (void*) data;
  attacker(args->attacker, args->keypair);
  return 0;
}

/*@
predicate_family_instance pthread_run_pre(server_t)(void *data, any info) =
  [_]world(nsl_pub) &*&
  nsl_args_server(data, ?server) &*&
  nsl_args_key_S_priv(data, ?key_S_priv) &*&
    item(key_S_priv, ?s_priv, nsl_pub) &*&
    s_priv == private_key_item(server, 1) &*&
  !bad(server) &*&
  generated_values(server, _) &*&
  info == cons(server, nil);
predicate_family_instance pthread_run_post(server_t)(void *data, any info) =
  [_]world(nsl_pub) &*&
  nsl_args_server(data, ?server) &*&
  nsl_args_key_S_priv(data, ?key_S_priv) &*&
  generated_values(server, _) &*&
  info == cons(server, nil);
@*/

void *server_t(void* data) //@ : pthread_run_joinable
  //@ requires pthread_run_pre(server_t)(data, ?x);
  //@ ensures pthread_run_post(server_t)(data, x) &*& result == 0;
{
  struct nsl_args *args = data;
  //@ open pthread_run_pre(server_t)(data, _);
  server(args->server, args->key_S_priv);
  item_free(args->key_S_priv);
  //@ close pthread_run_post(server_t)(data, _);

  return 0;
}

/*@
predicate_family_instance pthread_run_pre(receiver_t)(void *data, any info) =
  [_]world(nsl_pub) &*&
  nsl_args_receiver(data, ?receiver) &*&
  nsl_args_server(data, ?server) &*&
  nsl_args_key_B_priv(data, ?key_B_priv) &*&
    item(key_B_priv, ?b_priv, nsl_pub) &*&
    b_priv == private_key_item(receiver, 1) &*&
  nsl_args_key_S_pub(data, ?key_S_pub) &*&
    item(key_S_pub, ?s_pub, nsl_pub) &*&
    s_pub == public_key_item(server, 1) &*&
 !bad(receiver) &*& !bad(server) &*&
  generated_values(receiver, _) &*&
  info == cons(receiver, cons(server, nil));
predicate_family_instance pthread_run_post(receiver_t)(void *data, any info) =
  [_]world(nsl_pub) &*&
  nsl_args_receiver(data, ?receiver) &*&
  nsl_args_server(data, ?server) &*&
  nsl_args_key_B_priv(data, ?key_B_priv) &*&
  nsl_args_key_S_pub(data, ?key_S_pub) &*&
  generated_values(receiver, _) &*&
  info == cons(receiver, cons(server, nil));
@*/

void *receiver_t(void* data) //@ : pthread_run_joinable
  //@ requires pthread_run_pre(receiver_t)(data, ?x);
  //@ ensures pthread_run_post(receiver_t)(data, x) &*& result == 0;
{
  struct nsl_args *args = data;
  struct item *NA;
  struct item *NB;  
  //@ open pthread_run_pre(receiver_t)(data, _);
  int sender = receiver(args->receiver, args->server, args->key_B_priv, 
                        args->key_S_pub, &NA, &NB);
  item_free(args->key_B_priv);
  item_free(args->key_S_pub);
  /*@ if (!collision_in_run() && !bad(sender))
      {
        assert pointer(&NB, ?NBP);
        assert item (NBP, ?nb, _);
        leak is_not_public(_, nsl_pub, nb, _);
        assert pointer(&NA, ?NAP);
        assert item (NAP, ?na, _);
        leak is_not_public(_, nsl_pub, na, _);
      }
  @*/
  item_free(NA);
  item_free(NB);
  //@ close pthread_run_post(receiver_t)(data, _);
  return 0;
}


/*@
predicate_family_instance pthread_run_pre(sender_t)(void *data, any info) =
  [_]world(nsl_pub) &*&
  nsl_args_sender(data, ?sender) &*&
  nsl_args_receiver(data, ?receiver) &*&
  nsl_args_server(data, ?server) &*&
  nsl_args_key_A_priv(data, ?key_A_priv) &*&
    item(key_A_priv, ?a_priv, nsl_pub) &*&
    a_priv == private_key_item(sender, 1) &*&
  nsl_args_key_S_pub(data, ?key_S_pub) &*&
    item(key_S_pub, ?s_pub, nsl_pub) &*&
    s_pub == public_key_item(server, 1) &*&
 !bad(sender) &*& !bad(receiver) &*& !bad(server) &*&
  generated_values(sender, _) &*&
  info == cons(sender, cons(receiver, cons(server, nil)));
predicate_family_instance pthread_run_post(sender_t)(void *data, any info) =
  [_]world(nsl_pub) &*&
  nsl_args_sender(data, ?sender) &*&
  nsl_args_receiver(data, ?receiver) &*&
  nsl_args_server(data, ?server) &*&
  nsl_args_key_A_priv(data, ?key_A_priv) &*&
  nsl_args_key_S_pub(data, ?key_S_pub) &*&
  generated_values(sender, _) &*&
  info == cons(sender, cons(receiver, cons(server, nil)));
@*/



void *sender_t(void* data) //@ : pthread_run_joinable
  //@ requires pthread_run_pre(sender_t)(data, ?x);
  //@ ensures pthread_run_post(sender_t)(data, x) &*& result == 0;
{
  struct nsl_args *args = data;
  struct item *NA;
  struct item *NB;  
  //@ open pthread_run_pre(sender_t)(data, _);
  sender(args->sender, args->receiver, args->server, 
         args->key_A_priv, args->key_S_pub, &NA, &NB);
  item_free(args->key_A_priv);
  item_free(args->key_S_pub);
  /*@ if (!collision_in_run())
      {
        assert pointer(&NA, ?NAP);
        assert item (NAP, ?na, _);
        leak is_not_public(_, nsl_pub, na, _);
        assert pointer(&NB, ?NBP);
        assert item (NBP, ?nb, _);
        leak is_not_public(_, nsl_pub, nb, _);
      }
  @*/
  item_free(NA);
  item_free(NB);
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
  struct item *key_S_pub;
  struct item *key_S_priv;
  struct item *key_A_priv;
  struct item *key_B_priv;

  printf("\n\tExecuting \"");
  printf("nsl protocol");
  printf("\" ... \n\n");
  
  //@ open_module();
  //@ PACK_PROOF_OBLIGATIONS(nsl)
  init_crypto_lib();

  int attacker = create_principal(&apair);
  //@ assume (bad(attacker));
  int server_ = create_principal(&server_pair);
  char server = (char) server_;
  key_S_pub = keypair_get_public_key(server_pair);
  key_S_priv = keypair_get_private_key(server_pair);
  keypair_free(server_pair);
  int sender_ = create_principal(&sender_pair);
  char sender = (char) sender_;
  key_A_priv = keypair_get_private_key(sender_pair);
  keypair_free(sender_pair);
  int receiver_ = create_principal(&receiver_pair);
  char receiver = (char) receiver_;
  key_B_priv = keypair_get_private_key(receiver_pair);
  keypair_free(receiver_pair);
  //@ leak  world(nsl_pub);
  
  //@ assume (!bad(server) && !bad(sender) && !bad(receiver));
  void *null = (void *) 0;

  { 
    pthread_t a_thread;
    struct nsl_args *args = malloc(sizeof(struct nsl_args));
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
              [_]world(nsl_pub) &*&
              !bad(server) && !bad(sender) && !bad(receiver) &*&
              generated_values(server, _) &*&
              generated_values(sender, _) &*&
              generated_values(receiver, _) &*&
              item(key_S_pub, ?kkey_S_pub, nsl_pub) &*& 
              item(key_S_priv, ?kkey_S_priv, nsl_pub) &*& 
              item(key_A_priv, ?kkey_A_priv, nsl_pub) &*& 
              item(key_B_priv, ?kkey_B_priv, nsl_pub) &*& 
              kkey_S_pub == public_key_item(server, 1) &*&
              kkey_S_priv == private_key_item(server, 1) &*&
              kkey_A_priv == private_key_item(sender, 1) &*&
              kkey_B_priv == private_key_item(receiver, 1);
    @*/
  {
    pthread_t serv_thread, send_thread, rec_thread;
    struct nsl_args serv_args, send_args, rec_args;
    {
      serv_args.server = server;
      serv_args.key_S_priv = item_clone(key_S_priv);
      //@ close pthread_run_pre(server_t)(&serv_args, _);
      pthread_create(&serv_thread, null, &server_t, &serv_args);

      rec_args.receiver = receiver;
      rec_args.server = server;
      rec_args.key_B_priv = item_clone(key_B_priv);
      rec_args.key_S_pub = item_clone(key_S_pub);
      /*@ close pthread_run_pre(receiver_t)
                               (&rec_args, cons(receiver, cons(server, nil))); @*/
      pthread_create(&rec_thread, null, &receiver_t, &rec_args);

      send_args.sender = sender;
      send_args.receiver = receiver;
      send_args.server = server;
      send_args.key_A_priv = item_clone(key_A_priv);
      send_args.key_S_pub = item_clone(key_S_pub);
      /*@ close pthread_run_pre(sender_t)
                               (&send_args, cons(sender, cons(receiver, cons(server, nil)))); @*/
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
