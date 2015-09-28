#include "rpc.h"

#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define KEY_SIZE 16

//@ import_module public_invariant_mod;
//@ import_module principals_mod;

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
  //@ int client;
  //@ int server;
  
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

predicate_family_instance pthread_run_pre(client_t)(void *data, any info) =
  [_]public_invar(rpc_pub) &*&
  rpc_args_client(data, ?client) &*&
  rpc_args_server(data, ?server) &*&
  rpc_args_key(data, ?key) &*&
  principal(client, _) &*&
  [1/2]cryptogram(key, KEY_SIZE, ?key_cs, ?key_cg) &*&
    key_cg == cg_symmetric_key(client, ?id) &*&
    shared_with(client, id) == server &*&
  rpc_args_request(data, ?req) &*&
    [1/2]chars(req, PACKAGE_SIZE, ?req_cs) &*&
    request(client, server, req_cs) == true &*&
  rpc_args_response(data, ?resp) &*&
    chars(resp, PACKAGE_SIZE, _) &*&
  info == cons(int_value(client), 
            cons(int_value(server), 
              cons(pointer_value(key), 
                cons(char_list_value(key_cs),
                  cons(int_value(id),
                    cons(pointer_value(req),
                      cons(pointer_value(resp),
                           nil)))))));

predicate_family_instance pthread_run_post(client_t)(void *data, any info) =
  rpc_args_client(data, ?client) &*&
  rpc_args_server(data, ?server) &*&
  rpc_args_key(data, ?key) &*&
  principal(client, _) &*&
  [1/2]cryptogram(key, KEY_SIZE, ?key_cs, ?key_cg) &*&
    key_cg == cg_symmetric_key(client, ?id) &*&
  rpc_args_request(data, ?req) &*&
    [1/2]chars(req, PACKAGE_SIZE, ?req_cs) &*&
  rpc_args_response(data, ?resp) &*&
    chars(resp, PACKAGE_SIZE, ?resp_cs) &*&
    collision_in_run || bad(client) || bad(server) ||
    response(client, server, req_cs, resp_cs) &*&
  info == cons(int_value(client), 
            cons(int_value(server), 
              cons(pointer_value(key),
                cons(char_list_value(key_cs),
                  cons(int_value(id),
                    cons(pointer_value(req), 
                      cons(pointer_value(resp),                   
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

/*@

predicate_family_instance pthread_run_pre(server_t)(void *data, any info) =
  [_]public_invar(rpc_pub) &*&
  rpc_args_server(data, ?server) &*&
  rpc_args_client(data, ?client) &*&
  rpc_args_key(data, ?key) &*&
  principal(server, _) &*&
  [1/2]cryptogram(key, KEY_SIZE, ?key_cs, ?key_cg) &*&
    key_cg == cg_symmetric_key(client, ?id) &*&
    shared_with(client, id) == server &*&
  rpc_args_request(data, ?req) &*&
    chars(req, PACKAGE_SIZE, _) &*&
  rpc_args_response(data, ?resp) &*&
    chars(resp, PACKAGE_SIZE, _) &*&
  info == cons(int_value(client), 
            cons(int_value(server), 
              cons(pointer_value(key),
                cons(char_list_value(key_cs), 
                  cons(int_value(id),
                    cons(pointer_value(req),
                      cons(pointer_value(resp),
                           nil)))))));

predicate_family_instance pthread_run_post(server_t)(void *data, any info) =
  rpc_args_client(data, ?client) &*&
  rpc_args_server(data, ?server) &*&
  rpc_args_key(data, ?key) &*&
  principal(server, _) &*&
  [1/2]cryptogram(key, KEY_SIZE, ?key_cs, ?key_cg) &*&
    key_cg == cg_symmetric_key(client, ?id) &*&
  rpc_args_request(data, ?req) &*&
    chars(req, PACKAGE_SIZE, ?req_cs) &*&
    collision_in_run ||
    bad(client) || request(client, server, req_cs) &*&
  rpc_args_response(data, ?resp) &*&
    chars(resp, PACKAGE_SIZE, ?resp_cs) &*&
    collision_in_run || bad(client) || bad(server) || 
    response(client, server, req_cs, resp_cs) == true &*&
  info == cons(int_value(client), 
            cons(int_value(server), 
              cons(pointer_value(key), 
                cons(char_list_value(key_cs),
                  cons(int_value(id),
                    cons(pointer_value(req),
                      cons(pointer_value(resp),
                           nil)))))));
@*/

void *server_t(void* data) //@ : pthread_run_joinable
  //@ requires pthread_run_pre(server_t)(data, ?x);
  //@ ensures pthread_run_post(server_t)(data, x) &*& result == 0;
{
  struct rpc_args *args = data;
  //@ open pthread_run_pre(server_t)(data, _);
  server(args->key, KEY_SIZE, args->request, args->response);
  //@ close pthread_run_post(server_t)(data, _);
  return 0;
}

int main(int argc, char **argv) //@ : main_full(main_app)
    //@ requires module(main_app, true);
    //@ ensures true;
{
  //@ open_module();
  
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
                  principal(client, ?count_c) &*&
                  principal(server, ?count_s);
    @*/
  {
    char key[KEY_SIZE];
    char c_request[PACKAGE_SIZE];
    char c_response[PACKAGE_SIZE];
    char s_request[PACKAGE_SIZE];
    char s_response[PACKAGE_SIZE];
    int temp;
    int message_len;
  
    //@ close random_request(client, 0, true);
    if (havege_random(&havege_state, key, KEY_SIZE) != 0) abort();
    //@ assume (shared_with(client, count_c + 1) == server);
    //@ assert cryptogram(key, KEY_SIZE, ?cs_key, ?cg_key);
    //@ assert cg_key == cg_symmetric_key(client, count_c + 1);
    
    //@ close random_request(client, 0, false);
    if (havege_random(&havege_state, c_request, PACKAGE_SIZE) != 0) abort();
    //@ assert cryptogram(c_request, PACKAGE_SIZE, ?msg_cs, ?cg);
    //@ close rpc_pub(cg);
    //@ leak rpc_pub(cg);
    //@ public_cryptogram(c_request, cg);
    {
      pthread_t c_thread, s_thread;

      struct rpc_args c_args;
      struct rpc_args s_args;

      //@ c_args.client = client;
      //@ c_args.server = server;
      c_args.key = key;
      c_args.request = c_request;
      c_args.response = c_response;
      
      //@ s_args.client = client;
      //@ s_args.server = server;
      s_args.key = key;
      s_args.request = s_request;
      s_args.response = s_response;
      
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
      
      //@ close optional_crypto_chars(false, c_request, PACKAGE_SIZE, _);
      //@ close optional_crypto_chars(false, s_request, PACKAGE_SIZE, _);
      if (memcmp(c_request, s_request, PACKAGE_SIZE) != 0)
        abort();
      //@ close optional_crypto_chars(false, c_response, PACKAGE_SIZE, _);
      //@ close optional_crypto_chars(false, s_response, PACKAGE_SIZE, _);
      if (memcmp(c_response, s_response, PACKAGE_SIZE) != 0)
        abort();
    }
    //@ close optional_crypto_chars(!collision_in_run, key, KEY_SIZE, cs_key);
    zeroize(key, KEY_SIZE);
    
    printf(" |%i| ", i);
  }
  
  printf("\n\n\t\tDone\n");
  return 0;
}

