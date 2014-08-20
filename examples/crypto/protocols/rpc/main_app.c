#include "rpc.h"

#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>

//@ import_module cryptolib;

/*@
predicate_family_instance pthread_run_pre(attacker_t)(void *data, any info) =
    exists(rpc_pub) &*& [_]world(rpc_pub) &*&
    attacker_proof_obligations(rpc_pub) &*& 
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

struct rpc_args
{
  int server;
  int client;
  struct item *key;
  struct item *request;
};

/*@
predicate_family_instance pthread_run_pre(server_t)(void *data, any info) =
  [_]world(rpc_pub) &*&
  rpc_args_server(data, ?server) &*&
  rpc_args_client(data, ?client) &*&
  rpc_args_key(data, ?key) &*&
  generated_values(server, _) &*&
  item(key, key_item(client, ?id, symmetric_key, ?i)) &*&
  shared_with(client, id) == server &*&
  info == cons(server, nil);
predicate_family_instance pthread_run_post(server_t)(void *data, any info) =
  [_]world(rpc_pub) &*&
  rpc_args_server(data, ?server) &*&
  rpc_args_client(data, ?client) &*&
  rpc_args_key(data, ?key) &*&
  generated_values(server, _) &*&
  info == cons(server, nil);
@*/

void *server_t(void* data) //@ : pthread_run_joinable
  //@ requires pthread_run_pre(server_t)(data, ?x);
  //@ ensures pthread_run_post(server_t)(data, x) &*& result == 0;
{
  struct rpc_args *args = data;
  //@ open pthread_run_pre(server_t)(data, _);
  server(args->server, args->key);
  item_free(args->key);
  //@ close pthread_run_post(server_t)(data, _);
  return 0;
}

/*@
predicate_family_instance pthread_run_pre(client_t)(void *data, any info) =
  [_]world(rpc_pub) &*&
  rpc_args_server(data, ?server) &*&
  rpc_args_client(data, ?client) &*&
  rpc_args_key(data, ?key) &*&
  rpc_args_request(data, ?req) &*&
  item(key, key_item(client, ?id, symmetric_key, int_pair(0, 0))) &*&
  item(req, ?item) &*& rpc_pub(item) == true &*&
  request(client, server, item) == true &*&
  shared_with(client, id) == server &*&
  info == nil;
predicate_family_instance pthread_run_post(client_t)(void *data, any info) =
  rpc_args_server(data, ?server) &*&
  rpc_args_client(data, ?client) &*&
  rpc_args_key(data, ?key) &*&
  rpc_args_request(data, ?req) &*&
  info == nil;
@*/

void *client_t(void* data) //@ : pthread_run_joinable
  //@ requires pthread_run_pre(client_t)(data, ?x);
  //@ ensures pthread_run_post(client_t)(data, x) &*& result == 0;
{
  struct rpc_args *args = data;
  //@ open pthread_run_pre(client_t)(data, _);
  struct item *response = client(args->server, args->key, args->request);
  item_free(args->request);
  item_free(response);
  item_free(args->key);
  //@ close pthread_run_post(client_t)(data, _);
  return 0;
}

int main() //@ : main_full(main_app)
  //@ requires module(main_app, true);
  //@ ensures  true;
{
  printf("\n\tExecuting \"rpc protocol\" ... \n\n");
  //@ open_module();
  //@ close exists(rpc_pub);
  init_crypto_lib();

  //@ open initial_principals();
  int client = create_principal();
  //@ close key_request(client, int_pair(0, 0));
  struct item* key = create_symmetric_key();
  int server = create_principal();
  //@ assert item(key, key_item(_, ?id, _, _));
  //@ assume (shared_with(client, id) == server);

  void *null = (void *) 0;

  {
    pthread_t a_thread;
    //@ PACK_ATTACKER_PROOF_OBLIGATIONS(rpc)
    //@ close attacker_proof_obligations(rpc_pub);
    //@ leak  world(rpc_pub);
    //@ close pthread_run_pre(attacker_t)(null, _);
    pthread_create(&a_thread, null, &attacker_t, null);
  }

  int i = 0;
#ifdef EXECUTE
  while (i++ < 10)
#else
  while (true)
#endif
    /*@ invariant [_]world(rpc_pub) &*&
                  shared_with(client, id) == server &*&
                  generated_values(server, ?count) &*&
                  item(key, key_item(client, id, symmetric_key, int_pair(0, 0)));
    @*/
  {
    pthread_t s_thread, c_thread;
    struct rpc_args s_args, c_args;
    struct item *temp_key;
    {
      c_args.client = client;
      c_args.server = server;
      temp_key = item_clone(key);
      c_args.key = temp_key;
      int random = random_int();
      struct item *req = create_data_item(random);
      //@ assert item(req, ?request);
      c_args.request = req;
      //@ assume (request(client, server, request) == true);
      //@ close pthread_run_pre(client_t)(&c_args, _);
      pthread_create(&c_thread, null, &client_t, &c_args);

      s_args.client = client;
      s_args.server = server;
      temp_key = item_clone(key);
      s_args.key = temp_key;
      //@ close pthread_run_pre(server_t)(&s_args, cons(server, nil));
      pthread_create(&s_thread, null, &server_t, &s_args);
    }

    {
      pthread_join(c_thread, null);
      //@ open pthread_run_post(client_t)(&c_args, _);
      pthread_join(s_thread, null);
      //@ open pthread_run_post(server_t)(&s_args, cons(server, nil));
    }
  }

  //@ close_module();
  //@ leak module(main_app, _);
  printf("Done\n");
}
