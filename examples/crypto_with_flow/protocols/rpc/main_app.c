#include "rpc.h"

#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>

#define KEY_SIZE 16

//@ import_module public_invariant;

/*@
predicate rpc_proof_pred() = true;

predicate_family_instance pthread_run_pre(attacker_t)(void *data, any info) =
    [_]public_invar(rpc_pub) &*&
    public_invariant_constraints(rpc_pub, rpc_proof_pred) &*&
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
    //@ close rpc_proof_pred();
    attacker();
    //@ open rpc_proof_pred();
    //@ close pthread_run_pre(attacker_t)(data, info);
  }
   
  return 0;
}

struct rpc_args
{
  //@ int server;
  //@ int client;
  
  char* key;
  char* request;
  char* response;
};

/*@
inductive info =
  | int_value(int v)
  | pointer_value(char* p)
  | char_list_value(list<char> p)
;

predicate_family_instance pthread_run_pre(server_t)(void *data, any info) =
  [_]public_invar(rpc_pub) &*&
  rpc_args_server(data, ?server) &*&
  rpc_args_client(data, ?client) &*&
  rpc_args_key(data, ?key) &*&
    [1/2]cryptogram(key, KEY_SIZE, ?key_cs, ?key_cg) &*&
    key_cg == cg_symmetric_key(client, ?id) &*&
  generated_values(server, _) &*&
  shared_with(client, id) == server &*&
  info == cons(int_value(server), 
            cons(int_value(client), 
              cons(pointer_value(key),
                cons(char_list_value(key_cs), 
                  cons(int_value(id),
                       nil)))));
predicate_family_instance pthread_run_post(server_t)(void *data, any info) =
  rpc_args_server(data, ?server) &*&
  rpc_args_client(data, ?client) &*&
  rpc_args_key(data, ?key) &*&
    [1/2]cryptogram(key, KEY_SIZE, ?key_cs, ?key_cg) &*&
    key_cg == cg_symmetric_key(client, ?id) &*&
  generated_values(server, _) &*&
  info == cons(int_value(server), 
            cons(int_value(client), 
              cons(pointer_value(key), 
                cons(char_list_value(key_cs),
                  cons(int_value(id),
                       nil)))));
@*/

void *server_t(void* data) //@ : pthread_run_joinable
  //@ requires pthread_run_pre(server_t)(data, ?x);
  //@ ensures pthread_run_post(server_t)(data, x) &*& result == 0;
{
  struct rpc_args *args = data;
  //@ open pthread_run_pre(server_t)(data, _);
  server(args->key, KEY_SIZE);
  //@ close pthread_run_post(server_t)(data, _);
  return 0;
}

/*@
predicate_family_instance pthread_run_pre(client_t)(void *data, any info) =
  [_]public_invar(rpc_pub) &*&
  rpc_args_server(data, ?server) &*&
  rpc_args_client(data, ?client) &*&
  rpc_args_key(data, ?key) &*&
    [1/2]cryptogram(key, KEY_SIZE, ?key_cs, ?key_cg) &*&
    key_cg == cg_symmetric_key(client, ?id) &*&
  rpc_args_request(data, ?req) &*&
    [1/2]chars(req, PACKAGE_SIZE, ?req_cs) &*&
    request(client, server, req_cs) == true &*&
  rpc_args_response(data, ?resp) &*&
    chars(resp, PACKAGE_SIZE, _) &*&
  shared_with(client, id) == server &*&
  info == cons(int_value(server), 
            cons(int_value(client), 
              cons(pointer_value(key), 
                cons(char_list_value(key_cs),
                  cons(pointer_value(req),
                    cons(pointer_value(resp), 
                      cons(int_value(id),
                           nil)))))));
predicate_family_instance pthread_run_post(client_t)(void *data, any info) =
  rpc_args_server(data, ?server) &*&
  rpc_args_client(data, ?client) &*&
  rpc_args_key(data, ?key) &*&
    [1/2]cryptogram(key, KEY_SIZE, ?key_cs, ?key_cg) &*&
    key_cg == cg_symmetric_key(client, ?id) &*&
  rpc_args_request(data, ?req) &*&
    [1/2]chars(req, PACKAGE_SIZE, ?req_cs) &*&
  rpc_args_response(data, ?resp) &*&
    chars(resp, PACKAGE_SIZE, ?resp_cs) &*&
    (
      bad(client) || bad(server) ?
        true
      :
        true == response(client, server, req_cs, resp_cs)
    )
    &*&
  info == cons(int_value(server), 
            cons(int_value(client), 
              cons(pointer_value(key),
                cons(char_list_value(key_cs),
                  cons(pointer_value(req), 
                    cons(pointer_value(resp), 
                      cons(int_value(id),
                           nil)))))));
@*/

void *client_t(void* data) //@ : pthread_run_joinable
  //@ requires pthread_run_pre(client_t)(data, ?x);
  //@ ensures pthread_run_post(client_t)(data, x) &*& result == 0;
{
  struct rpc_args *args = data;
  //@ open pthread_run_pre(client_t)(data, _);
  client(args->key, KEY_SIZE, args->request, args->response);
  //@ close pthread_run_post(client_t)(data, _);
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
  printf("rpc protocol");
  printf("\" ... \n\n");
  
  //@ PUBLIC_INVARIANT_CONSTRAINTS(rpc)
  //@ public_invariant_init(rpc_pub);
  
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
    /*@ invariant [_]public_invar(rpc_pub) &*&
                  havege_state_initialized(&havege_state) &*&
                  generated_values(client, ?count_c) &*&
                  generated_values(server, ?count_s);
    @*/
  {
    char* key;
    char request[PACKAGE_SIZE];
    char response[PACKAGE_SIZE];
    int temp;
    int message_len;
  
    //@ close random_request(client, 0, true);
    key = malloc(KEY_SIZE);
    if (key == 0) abort();
    if (havege_random(&havege_state, key, KEY_SIZE) != 0) abort();
    //@ assume (shared_with(client, count_c + 1) == server);
    //@ assert cryptogram(key, KEY_SIZE, ?cs_key, ?cg_key);
    //@ assert cg_key == cg_symmetric_key(client, count_c + 1);
    //@ assert chars(request, PACKAGE_SIZE, ?msg_cs);
    {
      pthread_t s_thread, c_thread;

      struct rpc_args s_args;\
      struct rpc_args c_args;

      //@ s_args.client = client;
      //@ s_args.server = server;
      s_args.key = key;
      
      //@ c_args.client = client;
      //@ c_args.server = server;
      c_args.key = key;
      c_args.request = request;
      c_args.response = response;
      //@ assume (request(client, server, msg_cs) == true);
      //@ close pthread_run_pre(server_t)(&s_args, ?s_data);
      pthread_create(&s_thread, NULL, &server_t, &s_args);
      //@ close pthread_run_pre(client_t)(&c_args, ?c_data);
      pthread_create(&c_thread, NULL, &client_t, &c_args);
      
      pthread_join(s_thread, NULL);
      //@ open pthread_run_post(server_t)(&s_args, s_data);
      pthread_join(c_thread, NULL);
      //@ open pthread_run_post(client_t)(&c_args, c_data);  
      //@ open [1/2]cryptogram(key, KEY_SIZE, cs_key, _);
      //@ open [1/2]cryptogram(key, KEY_SIZE, cs_key, _);
    }
    //@ assert malloc_block(key, KEY_SIZE);
    //@ close optional_crypto_chars(true, key, KEY_SIZE, cs_key);
    free((void*) key);
  }
  
  printf("Done\n");
  return 0;
}

