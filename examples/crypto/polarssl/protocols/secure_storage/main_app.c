#include "secure_storage.h"

#include "../../src/random.h"

#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>

#define KEY_BYTE_SIZE 128

/*@
predicate ss_proof_pred() = true;

predicate_family_instance pthread_run_pre(attacker_t)(void *data, any info) =
    [1/3]polarssl_world(ss_polarssl_pub) &*&
    polarssl_proof_obligations(ss_polarssl_pub, ss_proof_pred) &*&
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
    //@ close ss_proof_pred();
    polarssl_attacker(data);
    //@ open ss_proof_pred();
    //@ close pthread_run_pre(attacker_t)(data, info);
  }
   
  return 0;
}

struct ss_args
{
  char* key;
  int key_len;
  char* message;
  int message_len;
};

/*@
inductive info =
  | int_value(int v)
  | pointer_value(char* p)
  | char_list(list<char> cs)
;

predicate_family_instance pthread_run_pre(sender_t)(void *data, any info) =
  [1/3]polarssl_world(ss_polarssl_pub) &*&
    ss_args_key(data, ?key) &*&
    ss_args_key_len(data, KEY_BYTE_SIZE) &*&
    ss_args_message(data, ?message) &*&
    ss_args_message_len(data, ?message_len) &*&
  [1/2]polarssl_cryptogram(key, KEY_BYTE_SIZE, ?key_cs, ?key_cg) &*&
    key_cg == polarssl_symmetric_key(?sender, ?id) &*&
  polarssl_public_message(ss_polarssl_pub)
                         (message, message_len, ?msg_cs) &*&
    message_len >= POLARSSL_MIN_HMAC_INPUT_BYTE_SIZE &*&
    message_len < POLARSSL_MAX_MESSAGE_BYTE_SIZE - 64 &*&
  malloc_block(message, message_len) &*&
  true == app_send_event(sender, msg_cs) &*&
  info == cons(int_value(sender), 
            cons(int_value(id), 
              cons(pointer_value(key),
                cons(char_list(msg_cs),
                  nil))));
predicate_family_instance pthread_run_post(sender_t)(void *data, any info) =
  [1/3]polarssl_world(ss_polarssl_pub) &*&
    ss_args_key(data, ?key) &*&
    ss_args_key_len(data, KEY_BYTE_SIZE) &*&
    ss_args_message(data, ?message) &*&
    ss_args_message_len(data, ?message_len) &*&
  [1/2]polarssl_cryptogram(key, KEY_BYTE_SIZE, ?key_cs, ?key_cg) &*&
    key_cg == polarssl_symmetric_key(?sender, ?id) &*&
  polarssl_public_message(ss_polarssl_pub)
                         (message, message_len, ?msg_cs) &*&
  malloc_block(message, message_len) &*&
  info == cons(int_value(sender), 
            cons(int_value(id), 
              cons(pointer_value(key), 
                cons(char_list(msg_cs),
                  nil))));
@*/

void *sender_t(void* data) //@ : pthread_run_joinable
  //@ requires pthread_run_pre(sender_t)(data, ?info);
  //@ ensures pthread_run_post(sender_t)(data, info) &*& result == 0;
{
  //@ open pthread_run_pre(sender_t)(data, _);
  struct ss_args *args = data;
  app_send(args->key, args->key_len, args->message, args->message_len);
  //@ close pthread_run_post(sender_t)(data, _);
  return 0;
}

/*@
predicate_family_instance pthread_run_pre(receiver_t)(void *data, any info) =
  [1/3]polarssl_world(ss_polarssl_pub) &*&
    ss_args_key(data, ?key) &*&
    ss_args_key_len(data, ?key_len) &*&
    ss_args_message(data, ?message) &*&
    ss_args_message_len(data, ?message_len) &*&
  [1/2]polarssl_cryptogram(key, key_len, ?key_cs, ?key_cg) &*&
    key_cg == polarssl_symmetric_key(?sender, ?id) &*&
  info == cons(int_value(sender), 
            cons(int_value(id), 
              cons(pointer_value(key), 
                nil)));
predicate_family_instance pthread_run_post(receiver_t)(void *data, any info) =
  [1/3]polarssl_world(ss_polarssl_pub) &*&
    ss_args_key(data, ?key) &*&
    ss_args_key_len(data, ?key_len) &*&
    ss_args_message(data, ?message) &*&
    ss_args_message_len(data, ?message_len) &*&
  [1/2]polarssl_cryptogram(key, key_len, ?key_cs, ?key_cg) &*&
    key_cg == polarssl_symmetric_key(?sender, ?id) &*&
  polarssl_public_message(ss_polarssl_pub)
                         (message, message_len, ?msg_cs) &*&
    malloc_block(message, message_len) &*&
    (bad(sender) ? true : true == app_send_event(sender, msg_cs)) &*&
  info == cons(int_value(sender), 
            cons(int_value(id), 
              cons(pointer_value(key), 
                nil)));
@*/

void *receiver_t(void* data) //@ : pthread_run_joinable
  //@ requires pthread_run_pre(receiver_t)(data, ?info);
  //@ ensures pthread_run_post(receiver_t)(data, info) &*& result == 0;
{
  //@ open pthread_run_pre(receiver_t)(data, info);
  struct ss_args *args = data;
  char* temp;
  args->message_len = app_receive(args->key, args->key_len, &temp);
  args->message = temp;
  //@ close pthread_run_post(receiver_t)(data, info);
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
  
  printf("\n\tExecuting \"secure_storage protocol\" ... \n\n");
  
  //@ PACK_PROOF_OBLIGATIONS(ss)
  //@ close exists(ss_polarssl_pub);
  //@ polarssl_init();
  
  //@ int sender = polarssl_create_principal();
  (*principals)++;
    //@ int receiver = polarssl_create_principal();
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
    /*@ invariant [2/3]polarssl_world(ss_polarssl_pub) &*& 
                  havege_state_initialized(&havege_state) &*&
                  polarssl_generated_values(sender, ?count_s);
    @*/
  {
    char* key;
    char* message;
    int temp;
    int message_len;
  
    //@ close random_request(sender, 0, true);
    key = malloc(KEY_BYTE_SIZE);
    if (key == 0) abort();
    if (havege_random(&havege_state, key, KEY_BYTE_SIZE) != 0) abort();
    
    r_int_with_bounds(&havege_state, &temp, 
                      POLARSSL_MIN_HMAC_INPUT_BYTE_SIZE, 
                      POLARSSL_MAX_MESSAGE_BYTE_SIZE - 65);
    message_len = temp;
    message = malloc(message_len);
    if (message == 0) abort();
    //@ assert chars(message, message_len, ?msg_cs);
    //@ polarssl_generated_public_cryptograms_assume(ss_polarssl_pub, msg_cs);
    {
      pthread_t s_thread, r_thread;
      
      struct ss_args s_args;
      struct ss_args r_args;
      
      /*@ open polarssl_cryptogram(key, KEY_BYTE_SIZE, ?key_cs,
                 polarssl_symmetric_key(sender, count_s + 1)); @*/
      //@ assert chars(key, KEY_BYTE_SIZE, ?cs_key);
      s_args.key_len = KEY_BYTE_SIZE;
      s_args.key = key;
      s_args.message_len = message_len;
      s_args.message = malloc(message_len);
      if (s_args.message == 0) abort();
      memcpy(s_args.message, message, (unsigned int) message_len);
      /*@ close polarssl_public_message(ss_polarssl_pub)
                   (s_args.message, message_len, msg_cs); @*/
      
      r_args.key_len = KEY_BYTE_SIZE;
      r_args.key = key;
      /*@ close polarssl_cryptogram(key, KEY_BYTE_SIZE, key_cs,
                  polarssl_symmetric_key(sender, count_s + 1)); @*/
      
      //@ assume (app_send_event(sender, msg_cs));
      
      //@ close pthread_run_pre(sender_t)(&s_args, _);
      pthread_create(&s_thread, NULL, &sender_t, &s_args);
      //@ close pthread_run_pre(receiver_t)(&r_args, _);
      pthread_create(&r_thread, NULL, &receiver_t, &r_args);
      
      pthread_join(s_thread, NULL);
      //@ open pthread_run_post(sender_t)(&s_args, _);
      pthread_join(r_thread, NULL);
      //@ open pthread_run_post(receiver_t)(&r_args, _);
      
      /*@ open polarssl_public_message(ss_polarssl_pub)
                                      (s_args.message, _, ?s_cs); @*/
      //@ assert true == app_send_event(sender, s_cs);
      free(s_args.message);
      /*@ open polarssl_public_message(ss_polarssl_pub)
                                      (r_args.message, _, ?r_cs); @*/
      /*@ if (!bad(sender))
          {
            assert true == app_send_event(sender, r_cs);
          } 
      @*/
      free(r_args.message);
      //@ open [1/2]polarssl_cryptogram(key, _, _, _);
      //@ open [1/2]polarssl_cryptogram(key, _, _, _);
    }
    
    free(key);
    free(message);
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
