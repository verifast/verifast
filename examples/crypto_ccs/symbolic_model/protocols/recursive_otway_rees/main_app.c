#include "recursive_otway_rees.h"

#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>

//@ import_module symbolic;

#define PART_PORT_1 111111
#define PART_PORT_2 222222
#define PART_PORT_3 333333
#define PART_PORT_4 444444

struct ror_args
{
  bool initial;

  int server;
  int principal;
  int next;
  int in_port;
  int out_port;

  struct item* key;
  struct keys* keys;
  struct keypair *keypair;
};

/*@
predicate_family_instance pthread_run_pre(attacker_t)(void *data, any info) =
    exists(ror_pub) &*& [_]world(ror_pub, ror_key_clsfy) &*&
    ror_args_principal(data, ?attacker) &*&
    true == bad(attacker) &*&
    principal(attacker, _) &*&
    ror_args_keypair(data, ?keypair) &*&
    keypair(keypair, attacker, _, ?i, ror_pub) &*&
    principals_created(_) &*& info == nil;
@*/

void *attacker_t(void* data) //@ : pthread_run_joinable
  //@ requires pthread_run_pre(attacker_t)(data, ?info);
  //@ ensures false;
{
  //@ open pthread_run_pre(attacker_t)(data, info);
  struct ror_args *args = (void*) data;
  symbolic_attacker(args->principal, args->keypair);
}

/*@
predicate_family_instance pthread_run_pre(server_t)(void *data, any info) =
  [_]world(ror_pub, ror_key_clsfy) &*&
  ror_args_server(data, ?server) &*&
    principal(server, _) &*&
  ror_args_keys(data, ?keys) &*&
    keys(server, keys) &*&
  ror_args_in_port(data, _) &*&
  info == cons(server, nil);
predicate_family_instance pthread_run_post(server_t)(void *data, any info) =
  ror_args_server(data, ?server) &*&
    principal(server, _) &*&
  ror_args_keys(data, ?keys) &*&
    keys(server, keys) &*&
  ror_args_in_port(data, _) &*&
  info == cons(server, nil);
@*/

void *server_t(void* data) //@ : pthread_run_joinable
  //@ requires pthread_run_pre(server_t)(data, ?x);
  //@ ensures pthread_run_post(server_t)(data, x) &*& result == 0;
{
  struct ror_args *args = data;
  //@ open pthread_run_pre(server_t)(data, _);
  server(args->server, args->keys, args->in_port);
  //@ close pthread_run_post(server_t)(data, _);
  return 0;
}

/*@
predicate_family_instance pthread_run_pre(participant_t)(void *data, any info) =
  [_]world(ror_pub, ror_key_clsfy) &*&
  ror_args_initial(data, ?initial) &*&
  ror_args_server(data, ?server) &*&
  ror_args_principal(data, ?principal) &*&
    principal(principal, _) &*&
  ror_args_next(data, ?next) &*&
  ror_args_in_port(data, _) &*&
  ror_args_out_port(data, _) &*&
  ror_args_key(data, ?key) &*&
    item(key, ?k, ror_pub) &*&
    k == symmetric_key_item(principal, _) &*&
    info_for_item(k) == int_pair(0, server) &*&
  info == cons(principal, nil);
predicate_family_instance pthread_run_post(participant_t)(void *data, any info) =
  ror_args_initial(data, ?initial) &*&
  ror_args_server(data, ?server) &*&
  ror_args_principal(data, ?principal) &*&
    principal(principal, _) &*&
  ror_args_next(data, ?next) &*&
  ror_args_in_port(data, ?in_port) &*&
  ror_args_out_port(data, ?out_port) &*&
  ror_args_key(data, ?key) &*&
    item(key, ?k, ror_pub) &*&
  info == cons(principal, nil);
@*/

void *participant_t(void* data) //@ : pthread_run_joinable
  //@ requires pthread_run_pre(participant_t)(data, ?x);
  //@ ensures pthread_run_post(participant_t)(data, x) &*& result == 0;
{
  struct ror_args *args = data;
  struct item *key1;
  struct item *key2;
  //@ open pthread_run_pre(participant_t)(data, _);
  participant(args->initial, args->server, args->principal, 
              args->next, args->in_port, args->out_port, args->key,
              &key1, &key2);
  if (!args->initial) item_free(key1);
  item_free(key2);
  //@ close pthread_run_post(participant_t)(data, _);
  return 0;
}

int main() //@ : main_full(main_app)
  //@ requires module(main_app, true);
  //@ ensures  true;
{
  struct keypair* pair;

  printf("\n\tExecuting \"");
  printf("ror protocol");
  printf("\" ... \n\n");

  //@ open_module();
  //@ PACK_PROOF_OBLIGATIONS(ror)
  init_crypto_lib();

  int p1 = create_principal(&pair); keypair_free(pair);
  int p2 = create_principal(&pair); keypair_free(pair);
  int p3 = create_principal(&pair); keypair_free(pair);
  int p4 = create_principal(&pair); keypair_free(pair);
  int server = create_principal(&pair); keypair_free(pair);
  int attacker = create_principal(&pair);
  //@ assume (bad(attacker));
  //@ leak  world(ror_pub, ror_key_clsfy);

  {
    pthread_t a_thread;
    struct ror_args *args = malloc(sizeof(struct ror_args));
    if (args == 0) abort();
    args->principal = attacker;
    args->keypair = pair;
    //@ close pthread_run_pre(attacker_t)(args, _);
    pthread_create(&a_thread, NULL, &attacker_t, args);
  }

  int i = 0;
#ifdef EXECUTE
  while (i++ < 10)
#else
  while (true)
#endif
    /*@ invariant [_]world(ror_pub, ror_key_clsfy) &*& 
                  principal(server, _) &*&
                  principal(p1, _) &*& principal(p2, _) &*&
                  principal(p3, _) &*& principal(p4, _); @*/
  {
    pthread_t tp1, tp2, tp3, tp4, ts;
    struct keys *keys = 0; //@ close keys(server, keys);
    struct ror_args args1, args2, args3, args4, argss;

    args1.initial = true; args1.server = server; args1.principal = p1;
    args1.in_port = PART_PORT_1; args1.out_port = PART_PORT_1;
    args2.initial = false; args2.server = server; args2.principal = p2;
    args2.in_port = PART_PORT_1; args2.out_port = PART_PORT_2;
    args3.initial = false; args3.server = server; args3.principal = p3;
    args3.in_port = PART_PORT_2; args3.out_port = PART_PORT_3;
    args4.initial = false; args4.server = server; args4.principal = p4;
    args4.in_port = PART_PORT_3; args4.out_port = PART_PORT_4;
    args1.next = p2; args2.next = p3; args3.next = p4; args4.next = server;

    //@ close key_request(p1, int_pair(0, server));
    args1.key = create_symmetric_key();
    keys = add_key(keys, item_clone(args1.key), p1);
    //@ close pthread_run_pre(participant_t)(&args1, cons(p1, nil));
    //@ close key_request(p2, int_pair(0, server));
    args2.key = create_symmetric_key();
    keys = add_key(keys, item_clone(args2.key), p2);
    //@ close pthread_run_pre(participant_t)(&args2, cons(p2, nil));
    //@ close key_request(p3, int_pair(0, server));
    args3.key = create_symmetric_key();
    keys = add_key(keys, item_clone(args3.key), p3);
    //@ close pthread_run_pre(participant_t)(&args3, cons(p3, nil));
    //@ close key_request(p4, int_pair(0, server));
    args4.key = create_symmetric_key();
    keys = add_key(keys, item_clone(args4.key), p4);
    //@ close pthread_run_pre(participant_t)(&args4, cons(p4, nil));

    argss.server = server;
    argss.keys = keys;
    argss.in_port = PART_PORT_4;
    //@ close pthread_run_pre(server_t)(&argss, cons(server, nil));

    {
      pthread_create(&ts, NULL, &server_t, &argss);
      pthread_create(&tp4, NULL, &participant_t, &args4);
      pthread_create(&tp3, NULL, &participant_t, &args3);
      pthread_create(&tp2, NULL, &participant_t, &args2);
      pthread_create(&tp1, NULL, &participant_t, &args1);
    }

    {
      pthread_join(tp1, NULL); pthread_join(tp2, NULL);
      pthread_join(tp3, NULL); pthread_join(tp4, NULL);
      pthread_join(ts, NULL);
    }

    //@ open pthread_run_post(participant_t)(&args1, cons(p1, nil));
    //@ open pthread_run_post(participant_t)(&args2, cons(p2, nil));
    //@ open pthread_run_post(participant_t)(&args3, cons(p3, nil));
    //@ open pthread_run_post(participant_t)(&args4, cons(p4, nil));
    item_free(args1.key); item_free(args2.key);
    item_free(args3.key); item_free(args4.key);
    //@ open pthread_run_post(server_t)(&argss, cons(server, nil));
    remove_keys(argss.keys);
  }
#ifdef EXECUTE
  //@ close_module();
  //@ leak module(main_app, _);
  printf("Done\n");
#endif
}
