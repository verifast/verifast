#include "sign.h"

#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define KEY_SIZE 128

//@ import_module public_invariant_mod;
//@ import_module principals_mod;

/*@
predicate sign_proof_pred() = true;

predicate_family_instance pthread_run_pre(attacker_t)(void *data, any info) =
    [_]public_invar(sign_pub) &*&
    public_invariant_constraints(sign_pub, sign_proof_pred) &*&
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
    //@ close sign_proof_pred();
    attacker();
    //@ open sign_proof_pred();
    //@ close pthread_run_pre(attacker_t)(data, info);
  }
   
  return 0;
}

struct sign_args
{
  //@ int sender;
  
  int receiver;
  char* key;
  char* message;
};

/*@
inductive info =
  | int_value(int v)
  | pointer_value(char* p)
  | char_list_value(list<char> p)
;

predicate_family_instance pthread_run_pre(sender_t)(void *data, any info) =
  [_]public_invar(sign_pub) &*&
  sign_args_sender(data, ?sender) &*&
  sign_args_receiver(data, ?receiver) &*&
  sign_args_key(data, ?key) &*&
  sign_args_message(data, ?msg) &*&
  principal(sender, _) &*&
  [1/2]cryptogram(key, 8 * KEY_SIZE, ?key_cs, ?key_cg) &*&
    key_cg == cg_private_key(sender, ?id) &*&
  chars(msg, MSG_SIZE, ?msg_cs) &*&
    true == send(sender, receiver, msg_cs) &*&
  info == cons(int_value(sender), 
            cons(int_value(receiver), 
              cons(pointer_value(key),
                cons(char_list_value(key_cs),
                  cons(int_value(id),
                    cons(pointer_value(msg),
                      cons(char_list_value(msg_cs),
                           nil)))))));

predicate_family_instance pthread_run_post(sender_t)(void *data, any info) =
  [_]public_invar(sign_pub) &*&
  sign_args_sender(data, ?sender) &*&
  sign_args_receiver(data, ?receiver) &*&
  sign_args_key(data, ?key) &*&
  sign_args_message(data, ?msg) &*&
  principal(sender, _) &*&
  [1/2]cryptogram(key, 8 * KEY_SIZE, ?key_cs, ?key_cg) &*&
    key_cg == cg_private_key(sender, ?id) &*&
  chars(msg, MSG_SIZE, ?msg_cs) &*&
    true == send(sender, receiver, msg_cs) &*&
  info == cons(int_value(sender), 
            cons(int_value(receiver), 
              cons(pointer_value(key),
                cons(char_list_value(key_cs),
                  cons(int_value(id),
                    cons(pointer_value(msg),
                      cons(char_list_value(msg_cs),
                           nil)))))));
@*/

void *sender_t(void* data) //@ : pthread_run_joinable
  //@ requires pthread_run_pre(sender_t)(data, ?x);
  //@ ensures pthread_run_post(sender_t)(data, x) &*& result == 0;
{
  struct sign_args *args = data;
  //@ open pthread_run_pre(sender_t)(data, _);
  sender(args->receiver, args->key, 8 * KEY_SIZE, args->message);
  //@ close pthread_run_post(sender_t)(data, _);
  return 0;
}

/*@

predicate_family_instance pthread_run_pre(receiver_t)(void *data, any info) =
  [_]public_invar(sign_pub) &*&
  sign_args_sender(data, ?sender) &*&
  sign_args_receiver(data, ?receiver) &*&
  sign_args_key(data, ?key) &*&
  sign_args_message(data, ?msg) &*&
  principal(receiver, _) &*&
  [1/2]cryptogram(key, 8 * KEY_SIZE, ?key_cs, ?key_cg) &*&
    key_cg == cg_public_key(sender, ?id) &*&
  chars(msg, MSG_SIZE, _) &*&
  info == cons(int_value(sender), 
            cons(int_value(receiver), 
              cons(pointer_value(key),
                cons(char_list_value(key_cs),
                  cons(int_value(id),
                    cons(pointer_value(msg),
                         nil))))));
                         
predicate_family_instance pthread_run_post(receiver_t)(void *data, any info) =
[_]public_invar(sign_pub) &*&
  sign_args_sender(data, ?sender) &*&
  sign_args_receiver(data, ?receiver) &*&
  sign_args_key(data, ?key) &*&
  sign_args_message(data, ?msg) &*&
  principal(receiver, _) &*&
  [1/2]cryptogram(key, 8 * KEY_SIZE, ?key_cs, ?key_cg) &*&
    key_cg == cg_public_key(sender, ?id) &*&
  chars(msg, MSG_SIZE, ?msg_cs) &*&
    bad(sender) || collision_in_run() || send(sender, receiver, msg_cs) &*&
  info == cons(int_value(sender), 
            cons(int_value(receiver), 
              cons(pointer_value(key),
                cons(char_list_value(key_cs),
                  cons(int_value(id),
                    cons(pointer_value(msg),
                         nil))))));
@*/

void *receiver_t(void* data) //@ : pthread_run_joinable
  //@ requires pthread_run_pre(receiver_t)(data, ?x);
  //@ ensures pthread_run_post(receiver_t)(data, x) &*& result == 0;
{
  struct sign_args *args = data;
  //@ open pthread_run_pre(receiver_t)(data, _);
  receiver(args->receiver, args->key, 8 * KEY_SIZE, args->message);
  //@ assert sign_args_sender(data, ?sender);
  //@ assert sign_args_receiver(data, ?receiver);
  //@ assert sign_args_message(data, ?msg);
  //@ assert chars(msg, MSG_SIZE, ?msg_cs);
  //@ assert bad(sender) || collision_in_run() || send(sender, receiver, msg_cs);
  //@ close pthread_run_post(receiver_t)(data, _);
  return 0;
}

int random_stub_main(void *havege_state, char *output, size_t len)
  //@ requires PRG_PRECONDITION(havege_state_initialized, havege_state);
  //@ ensures PRG_POSTCONDITION(havege_state_initialized, havege_state);
{
  return havege_random(havege_state, output, len);
}

int main(int argc, char **argv) //@ : main_full(main_app)
    //@ requires module(main_app, true);
    //@ ensures true;
{
  //@ open_module();

  pthread_t a_thread;
  havege_state havege_state;
  
  printf("\n\tExecuting \"");
  printf("sign protocol");
  printf("\" ... \n\n");
  
  //@ PUBLIC_INVARIANT_CONSTRAINTS(sign)
  //@ public_invariant_init(sign_pub);
  
  //@ principals_init();
  //@ int attacker = principal_create();
  //@ int sender = principal_create();
  //@ int receiver = principal_create();
  //@ assert receiver == 3;
  
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
    /*@ invariant [_]public_invar(sign_pub) &*&
                  havege_state_initialized(&havege_state) &*&
                  principal(sender, ?count) &*& principal(receiver, _); 
    @*/
  {
    pk_context context;
    char* priv_key;
    char* pub_key;
    
    unsigned int key_size = (unsigned int) 8 * KEY_SIZE;
    priv_key = malloc((int) key_size);
    if (priv_key == 0) abort();
    pub_key = malloc((int) key_size);
    if (pub_key == 0) abort();
    
    //@ close pk_context(&context);
    pk_init(&context);
    if (pk_init_ctx(&context, pk_info_from_type(POLARSSL_PK_RSA)) != 0)
      abort();
    //@ close rsa_key_request(sender, 0);
    //@ close random_state_predicate(havege_state_initialized);
    /*@ produce_function_pointer_chunk random_function(random_stub_main)
                     (havege_state_initialized)(state, out, len) { call(); } @*/
    if (rsa_gen_key(context.pk_ctx, random_stub_main, 
                    (void*) &havege_state, key_size, 65537) != 0)
      abort();
    if (pk_write_pubkey_pem(&context, pub_key, key_size) != 0) abort();
    if (pk_write_key_pem(&context, priv_key, key_size) != 0) abort();
    //@ assert cryptogram(priv_key, key_size, ?cs_priv_key, ?cg_priv_key);
    //@ assert cryptogram(pub_key, key_size, ?cs_pub_key, ?cg_pub_key);
    //@ assert cg_priv_key == cg_private_key(sender, count + 1);
    //@ assert cg_pub_key == cg_public_key(sender, count + 1);
    //@ open random_state_predicate(havege_state_initialized);
    //@ pk_release_context_with_keys(&context);
    pk_free(&context);
    //@ open pk_context(&context);
    {
      pthread_t s_thread, r_thread;

      struct sign_args s_args;
      struct sign_args r_args;
      char s_message[MSG_SIZE];
      char r_message[MSG_SIZE];
      
      //@ close random_request(sender, 0, false);
      if (havege_random(&havege_state, s_message, MSG_SIZE) != 0) abort();
      //@ assert cryptogram(s_message, MSG_SIZE, ?cs, ?cg);
      //@ close sign_pub(cg);
      //@ leak sign_pub(cg);
      //@ public_cryptogram(s_message, cg);
      //@ assume (send(sender, receiver, cs));
    
      //@ s_args.sender = sender;
      s_args.receiver = 3;
      s_args.key = priv_key;
      s_args.message = s_message;
      
      //@ r_args.sender = sender;
      r_args.receiver = 3;
      r_args.key = pub_key;
      r_args.message = r_message;
      
      //@ close pthread_run_pre(sender_t)(&s_args, ?s_data);
      //@ close pthread_run_pre(receiver_t)(&r_args, ?r_data);
      pthread_create(&r_thread, NULL, &receiver_t, &r_args);
      pthread_create(&s_thread, NULL, &sender_t, &s_args);
      
      pthread_join(s_thread, NULL);
      //@ open pthread_run_post(sender_t)(&s_args, s_data);
      pthread_join(r_thread, NULL);
      //@ open pthread_run_post(receiver_t)(&r_args, r_data);
    
      //@ close optional_crypto_chars(false, s_message, MSG_SIZE, _);
      //@ close optional_crypto_chars(false, r_message, MSG_SIZE, _);
      if (memcmp(s_message, r_message, MSG_SIZE) != 0)
        abort();
        
      printf(" |%i| ", i);
    }
    //@ open cryptogram(priv_key, 8 * KEY_SIZE, cs_priv_key, _);
    //@ close optional_crypto_chars(!collision_in_run, priv_key, 8 * KEY_SIZE, cs_priv_key);
    zeroize(priv_key, 8 * KEY_SIZE);
    free((void*) priv_key);
    //@ close sign_pub(cg_pub_key);
    //@ leak sign_pub(cg_pub_key);
    //@ close [1/2]cryptogram(pub_key, 8 * KEY_SIZE, cs_pub_key, cg_pub_key);
    //@ assert cryptogram(pub_key, 8 * KEY_SIZE, cs_pub_key, cg_pub_key);
    //@ public_cryptogram(pub_key, cg_pub_key);
    //@ assert chars(pub_key, 8 * KEY_SIZE, cs_pub_key);
    free((void*) pub_key);
  }
  
  printf("\n\n\t\tDone\n");
  return 0;
}

