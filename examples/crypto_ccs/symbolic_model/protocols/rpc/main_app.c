#include "rpc.h"

#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>

//@ import_module symbolic;

struct rpc_args
{
  int attacker;
  char server;
  char client;
  struct item *key;
  struct item *request;
  struct item *response;
  struct keypair *keypair;
};

/*@
predicate_family_instance pthread_run_pre(attacker_t)(void *data, any info) =
    [_]world(rpc_pub, rpc_key_clsfy) &*&
    rpc_args_attacker(data, ?attacker) &*&
    true == bad(attacker) &*&
    principal(attacker, _) &*&
    rpc_args_keypair(data, ?keypair) &*&    
    keypair(keypair, attacker, _, ?i, rpc_pub) &*&
    principals_created(_) &*& info == nil;
@*/

void *attacker_t(void* data) //@ : pthread_run_joinable
  //@ requires pthread_run_pre(attacker_t)(data, ?info);
  //@ ensures false;
{
  //@ open pthread_run_pre(attacker_t)(data, info);
  struct rpc_args *args = (void*) data;
  symbolic_attacker(args->attacker, args->keypair);
}

/*@
predicate_family_instance pthread_run_pre(server_t)(void *data, any info) =
  [_]world(rpc_pub, rpc_key_clsfy) &*&
  rpc_args_server(data, ?server) &*&
  rpc_args_client(data, ?client) &*&
  rpc_args_key(data, ?key) &*&
  principal(server, _) &*&
  item(key, symmetric_key_item(client, ?id), rpc_pub) &*&
  shared_with(client, id) == server &*&
  info == cons(server, nil);
predicate_family_instance pthread_run_post(server_t)(void *data, any info) =
  rpc_args_server(data, ?server) &*&
  rpc_args_client(data, ?client) &*&
  rpc_args_key(data, ?key) &*&
  principal(server, _) &*&
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
  [_]world(rpc_pub, rpc_key_clsfy) &*&
  rpc_args_server(data, ?server) &*&
  rpc_args_client(data, ?client) &*&
  rpc_args_key(data, ?key) &*&
  rpc_args_request(data, ?req) &*&
  principal(_, _) &*&
  item(key, symmetric_key_item(client, ?id), rpc_pub) &*&
  item(req, ?item, rpc_pub) &*& [_]rpc_pub(item) &*&
  true == well_formed_item(item) &*&
  request(client, server, item) == true &*&
  shared_with(client, id) == server &*&
  info == nil;
predicate_family_instance pthread_run_post(client_t)(void *data, any info) =
  rpc_args_server(data, ?server) &*&
  rpc_args_client(data, ?client) &*&
  rpc_args_key(data, ?key) &*&
  rpc_args_request(data, ?req) &*&
  principal(_, _) &*&
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
  struct keypair* apair;
  struct keypair* cpair;
  struct keypair* spair;
    
  printf("\n\tExecuting \"");
  printf("rpc protocol");
  printf("\" ... \n\n");
  
  //@ open_module();
  //@ PACK_PROOF_OBLIGATIONS(rpc)
  init_crypto_lib();
  
  int attacker = create_principal(&apair);
  //@ assume (bad(attacker));
  int client_ = create_principal(&cpair);
  keypair_free(cpair);
  char client = (char) client_;
  //@ close key_request(client, int_pair(0, 0));
  struct item* key = create_symmetric_key();
  int server_ = create_principal(&spair);
  keypair_free(spair);
  char server = (char) server_;
  //@ assert item(key, symmetric_key_item(_, ?id), rpc_pub);
  //@ assume (shared_with(client, id) == server);
  //@ leak  world(rpc_pub, rpc_key_clsfy);
  
  { 
    pthread_t a_thread;
    struct rpc_args *args = malloc(sizeof(struct rpc_args));
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
    /*@ invariant [_]world(rpc_pub, rpc_key_clsfy) &*&
                  shared_with(client, id) == server &*&
                  principal(server, ?count) &*& principal(_, _) &*&
                  item(key, symmetric_key_item(client, id), rpc_pub);
    @*/
  {
    pthread_t s_thread, c_thread;
    struct rpc_args s_args, c_args;
    struct item *temp_key;
    {
      //@ item n = nonce_item(server, count + 1, 0);
      //@ close rpc_pub(n);
      //@ leak rpc_pub(n);
      int random = random_int();
      c_args.client = client;
      c_args.server = server;
      temp_key = item_clone(key);
      c_args.key = temp_key;
      
      struct item *req = create_data_item((void*) &random, (int) sizeof(int));
      //@ assert item(req, ?request, rpc_pub);
      //@ close rpc_pub(request);
      //@ leak rpc_pub(request);
      c_args.request = req;
      //@ assume (request(client, server, request) == true);
      s_args.client = client;
      s_args.server = server;
      temp_key = item_clone(key);
      s_args.key = temp_key;
      //@ close pthread_run_pre(server_t)(&s_args, cons(server, nil));
      pthread_create(&s_thread, NULL, &server_t, &s_args);
      //@ close pthread_run_pre(client_t)(&c_args, _);
      pthread_create(&c_thread, NULL, &client_t, &c_args);
      //@ chars_to_integer(&random);
    }

    {
      pthread_join(c_thread, NULL);
      //@ open pthread_run_post(client_t)(&c_args, _);
      pthread_join(s_thread, NULL);
      //@ open pthread_run_post(server_t)(&s_args, cons(server, nil));
    }
  }
#ifdef EXECUTE
  //@ close_module();
  //@ leak module(main_app, _);
  printf("Done\n");
#endif
}
