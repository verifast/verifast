#include "rpc.h"

#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>

#define KEY_BYTE_SIZE 16

/*@
predicate rpc_proof_pred() = true;

predicate_family_instance pthread_run_pre(attacker_t)(void *data, any info) =
    [1/3]polarssl_world(rpc_polarssl_pub) &*&
    polarssl_proof_obligations(rpc_polarssl_pub, rpc_proof_pred) &*&
    integer(data, ?val) &*& val >= 0 &*&
    polarssl_principals(val) &*& info == nil;
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
    polarssl_attacker(data);
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
;

predicate_family_instance pthread_run_pre(server_t)(void *data, any info) =
  [1/3]polarssl_world(rpc_polarssl_pub) &*&
  rpc_args_server(data, ?server) &*&
  rpc_args_client(data, ?client) &*&
  rpc_args_key(data, ?key) &*&
    [1/2]polarssl_cryptogram(key, KEY_BYTE_SIZE, ?key_cs, ?key_cg) &*&
    key_cg == polarssl_symmetric_key(client, ?id) &*&
  polarssl_generated_values(server, _) &*&
  shared_with(client, id) == server &*&
  info == cons(int_value(server), 
            cons(int_value(client), 
              cons(pointer_value(key), 
                cons(int_value(id),
                  nil))));
predicate_family_instance pthread_run_post(server_t)(void *data, any info) =
  [1/3]polarssl_world(rpc_polarssl_pub) &*&
  rpc_args_server(data, ?server) &*&
  rpc_args_client(data, ?client) &*&
  rpc_args_key(data, ?key) &*&
    [1/2]polarssl_cryptogram(key, KEY_BYTE_SIZE, ?key_cs, ?key_cg) &*&
    key_cg == polarssl_symmetric_key(client, ?id) &*&
  polarssl_generated_values(server, _) &*&
  info == cons(int_value(server), 
            cons(int_value(client), 
              cons(pointer_value(key), 
                cons(int_value(id),
                  nil))));
@*/

void *server_t(void* data) //@ : pthread_run_joinable
  //@ requires pthread_run_pre(server_t)(data, ?x);
  //@ ensures pthread_run_post(server_t)(data, x) &*& result == 0;
{
  struct rpc_args *args = data;
  //@ open pthread_run_pre(server_t)(data, _);
  server(args->key, KEY_BYTE_SIZE);
  //@ close pthread_run_post(server_t)(data, _);
  return 0;
}

/*@
predicate_family_instance pthread_run_pre(client_t)(void *data, any info) =
  [1/3]polarssl_world(rpc_polarssl_pub) &*&
  rpc_args_server(data, ?server) &*&
  rpc_args_client(data, ?client) &*&
  rpc_args_key(data, ?key) &*&
    [1/2]polarssl_cryptogram(key, KEY_BYTE_SIZE, ?key_cs, ?key_cg) &*&
    key_cg == polarssl_symmetric_key(client, ?id) &*&
  rpc_args_request(data, ?req) &*&
    [1/2]polarssl_public_message
      (rpc_polarssl_pub)(req, PACKAGE_BYTE_SIZE, ?req_cs) &*&
    request(client, server, req_cs) == true &*&
  rpc_args_response(data, ?resp) &*&
    chars(resp, PACKAGE_BYTE_SIZE, _) &*&
  shared_with(client, id) == server &*&
  info == cons(int_value(server), 
            cons(int_value(client), 
              cons(pointer_value(key), 
                cons(pointer_value(req),
                  cons(pointer_value(resp), 
                    cons(int_value(id),
                      nil))))));
predicate_family_instance pthread_run_post(client_t)(void *data, any info) =
  [1/3]polarssl_world(rpc_polarssl_pub) &*&
  rpc_args_server(data, ?server) &*&
  rpc_args_client(data, ?client) &*&
  rpc_args_key(data, ?key) &*&
    [1/2]polarssl_cryptogram(key, KEY_BYTE_SIZE, ?key_cs, ?key_cg) &*&
    key_cg == polarssl_symmetric_key(client, ?id) &*&
  rpc_args_request(data, ?req) &*&
    [1/2]polarssl_public_message
      (rpc_polarssl_pub)(req, PACKAGE_BYTE_SIZE, ?req_cs) &*&
  rpc_args_response(data, ?resp) &*&
    polarssl_public_message
      (rpc_polarssl_pub)(resp, PACKAGE_BYTE_SIZE, ?resp_cs) &*&
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
                cons(pointer_value(req), 
                  cons(pointer_value(resp), 
                    cons(int_value(id),
                      nil))))));
@*/

void *client_t(void* data) //@ : pthread_run_joinable
  //@ requires pthread_run_pre(client_t)(data, ?x);
  //@ ensures pthread_run_post(client_t)(data, x) &*& result == 0;
{
  struct rpc_args *args = data;
  //@ open pthread_run_pre(client_t)(data, _);
  client(args->key, KEY_BYTE_SIZE, args->request, args->response);
  //@ close pthread_run_post(client_t)(data, _);
  return 0;
}

int main() //@ : main
  //@ requires true;
  //@ ensures  true;
{
  pthread_t a_thread;
  havege_state havege_state;
  int* principals = malloc(sizeof(int));
  if (principals == 0) abort();
  *principals = 0;
  
  printf("\n\tExecuting \"rpc protocol\" ... \n\n");
  
  //@ PACK_PROOF_OBLIGATIONS(rpc)
  //@ close exists(rpc_polarssl_pub);
  //@ polarssl_init();
  
  //@ int client = polarssl_create_principal();
  (*principals)++;
    //@ int server = polarssl_create_principal();
  (*principals)++;
  
  //@ close havege_state(&havege_state);
  havege_init(&havege_state);
  
  //@ close pthread_run_pre(attacker_t)(principals, _);
  pthread_create(&a_thread, NULL, &attacker_t, principals);
  
  int i = 0;
#ifdef EXECUTE
  while (i++ < 10)
#else
  while (true)
#endif
    /*@ invariant [2/3]polarssl_world(rpc_polarssl_pub) &*& 
                  havege_state_initialized(&havege_state) &*&
                  polarssl_generated_values(client, ?count_c) &*&
                  polarssl_generated_values(server, ?count_s);
    @*/
  {
    char* key;
    char request[PACKAGE_BYTE_SIZE];
    char response[PACKAGE_BYTE_SIZE];
    int temp;
    int message_len;
  
    //@ close random_request(client, 0, true);
    key = malloc(KEY_BYTE_SIZE);
    if (key == 0) abort();
    if (havege_random(&havege_state, key, KEY_BYTE_SIZE) != 0) abort();
    //@ assume (shared_with(client, count_c + 1) == server);
    
    //@ assert chars(request, PACKAGE_BYTE_SIZE, ?msg_cs);
    //@ polarssl_public_generated_chars_assume(rpc_polarssl_pub, msg_cs);
    /*@ close polarssl_public_message(rpc_polarssl_pub)
                                     (request, PACKAGE_BYTE_SIZE, msg_cs); @*/
    {
      pthread_t s_thread, c_thread;

      struct rpc_args s_args;\
      struct rpc_args c_args;

      /*@ assert polarssl_cryptogram(key, KEY_BYTE_SIZE, ?cs_key,
                             polarssl_symmetric_key(client, count_c + 1)); @*/
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
      //@ open [1/2]polarssl_cryptogram(key, KEY_BYTE_SIZE, _, _);
      //@ open [1/2]polarssl_cryptogram(key, KEY_BYTE_SIZE, _, _);
    }
    //@ assert chars(key, KEY_BYTE_SIZE, _);
    //@ assert malloc_block(key, KEY_BYTE_SIZE);
    free(key);
    
    /*@ open [1/2]polarssl_public_message(rpc_polarssl_pub)
                                         (request, PACKAGE_BYTE_SIZE, _); @*/
    /*@ open [1/2]polarssl_public_message(rpc_polarssl_pub)
                                         (request, PACKAGE_BYTE_SIZE, _); @*/
    //@ assert chars(request, PACKAGE_BYTE_SIZE, _);
    /*@ open polarssl_public_message(rpc_polarssl_pub)
                                    (response, PACKAGE_BYTE_SIZE, _); @*/
    //@ assert chars(response, PACKAGE_BYTE_SIZE, _);
  }
  
  //@ havege_exit(&havege_state);
  //@ open havege_state(&havege_state);
  
  //@ destroy_polarssl_principal(sender);
  //@ destroy_polarssl_principal(receiver);
  
  printf("Done\n");
  
  //@ leak malloc_block_ints(principals, 1);
  //@ leak [_]polarssl_world(_);
  return 0;
}

