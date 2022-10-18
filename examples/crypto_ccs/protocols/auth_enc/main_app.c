#include "auth_enc.h"

#include "../general.h"

#define MSG_LEN 64

//@ ATTACKER_PRE(auth_enc)

void *attacker_t(void* data) //@ : pthread_run_joinable
  //@ requires pthread_run_pre(attacker_t)(data, ?info);
  //@ ensures  false;
{
  while(true)
    //@ invariant pthread_run_pre(attacker_t)(data, info);
  {
    //@ open pthread_run_pre(attacker_t)(data, info);
    //@ close auth_enc_proof_pred();
    attacker();
    //@ open auth_enc_proof_pred();
    //@ close pthread_run_pre(attacker_t)(data, info);
  }
}

struct auth_enc_args
{
  //@ int sender;
  //@ int receiver;
  
  char* key;
  char* msg;
  
  int length;
};

/*@

predicate_family_instance pthread_run_pre(sender_t)(void *data, any info) =
  [_]public_invar(auth_enc_pub) &*&
  auth_enc_args_sender(data, ?sender) &*&
  auth_enc_args_receiver(data, ?receiver) &*&
  auth_enc_args_key(data, ?key) &*&
  auth_enc_args_msg(data, ?msg) &*& 
  !bad(sender) && !bad(receiver) &*&
  principal(sender, _) &*&
  [1/2]cryptogram(key, KEY_SIZE, ?key_ccs, ?key_cg) &*&
    key_cg == cg_symmetric_key(sender, ?id) &*&
    receiver == shared_with(sender, id) &*&
  crypto_chars(secret, msg, MSG_LEN, ?msg_ccs) &*&
    true == send(sender, receiver, msg_ccs) &*&
  info == IV(sender, IV(receiver, PV(key, CCL(key_ccs, 
             IV(id, PV(msg, CCL(msg_ccs, nil)))))));

predicate_family_instance pthread_run_post(sender_t)(void *data, any info) =
  [_]public_invar(auth_enc_pub) &*&
  auth_enc_args_sender(data, ?sender) &*&
  auth_enc_args_receiver(data, ?receiver) &*&
  auth_enc_args_key(data, ?key) &*&
  auth_enc_args_msg(data, ?msg) &*& 
  principal(sender, _) &*&
  [1/2]cryptogram(key, KEY_SIZE, ?key_ccs, ?key_cg) &*&
    key_cg == cg_symmetric_key(sender, ?id) &*&
    receiver == shared_with(sender, id) &*&
  crypto_chars(secret, msg, MSG_LEN, ?msg_ccs) &*&
  info == IV(sender, IV(receiver, PV(key, CCL(key_ccs, 
             IV(id, PV(msg, CCL(msg_ccs, nil)))))));
@*/

void *sender_t(void* data) //@ : pthread_run_joinable
  //@ requires pthread_run_pre(sender_t)(data, ?x);
  //@ ensures pthread_run_post(sender_t)(data, x) &*& result == 0;
{
  struct auth_enc_args *args = data;
  //@ open pthread_run_pre(sender_t)(data, _);
  sender(args->key,args->msg, MSG_LEN);
  //@ close pthread_run_post(sender_t)(data, _);
  return 0;
}

/*@

predicate_family_instance pthread_run_pre(receiver_t)(void *data, any info) =
  [_]public_invar(auth_enc_pub) &*&
  auth_enc_args_sender(data, ?sender) &*&
  auth_enc_args_receiver(data, ?receiver) &*&
  auth_enc_args_key(data, ?key) &*&
  auth_enc_args_msg(data, ?msg) &*& 
  auth_enc_args_length_(data, _) &*& 
  !bad(sender) && !bad(receiver) &*&
  principal(receiver, _) &*&
  [1/2]cryptogram(key, KEY_SIZE, ?key_ccs, ?key_cg) &*&
    key_cg == cg_symmetric_key(sender, ?id) &*&
    receiver == shared_with(sender, id) &*&
  chars_(msg, MAX_SIZE, _) &*&
  info == IV(sender, IV(receiver, PV(key, CCL(key_ccs, IV(id, PV(msg, nil))))));

predicate_family_instance pthread_run_post(receiver_t)(void *data, any info) =
  [_]public_invar(auth_enc_pub) &*&
  auth_enc_args_sender(data, ?sender) &*&
  auth_enc_args_receiver(data, ?receiver) &*&
  auth_enc_args_key(data, ?key) &*&
  auth_enc_args_msg(data, ?msg) &*&
  auth_enc_args_length(data, ?length) &*& 
  principal(receiver, _) &*&
  [1/2]cryptogram(key, KEY_SIZE, ?key_ccs, ?key_cg) &*&
    key_cg == cg_symmetric_key(sender, ?id) &*&
    receiver == shared_with(sender, id) &*&
  crypto_chars(secret, msg, length, ?msg_ccs) &*&
  chars_(msg + length, MAX_SIZE - length, _) &*&
  col || send(sender, receiver, msg_ccs) &*&
  info == IV(sender, IV(receiver, PV(key, CCL(key_ccs, IV(id, PV(msg, nil))))));
@*/

void *receiver_t(void* data) //@ : pthread_run_joinable
  //@ requires pthread_run_pre(receiver_t)(data, ?x);
  //@ ensures pthread_run_post(receiver_t)(data, x) &*& result == 0;
{
  struct auth_enc_args *args = data;
  //@ open pthread_run_pre(receiver_t)(data, _);
  args->length = receiver(args->key, args->msg);
  //@ close pthread_run_post(receiver_t)(data, _);
  return 0;
}

int main(int argc, char **argv) //@ : main_full(main_app)
    //@ requires module(main_app, true);
    //@ ensures true;
{
  pthread_t a_thread;
  havege_state havege_state;
  
  printf("\n\tExecuting \"");
  printf("auth_enc protocol");
  printf("\" ... \n\n");
  
  //@ PROTOCOL_INIT(auth_enc)
  //@ int attacker = principal_create();
  //@ int sender = principal_create();
  //@ int receiver = principal_create();
  //@ assume (!bad(sender) && !bad(receiver));
  
  //@ close havege_state(&havege_state);
  havege_init(&havege_state);
  //@ assume (bad(attacker));
  //@ close exists(attacker);
  //@ close pthread_run_pre(attacker_t)(NULL, some(attacker));
  pthread_create(&a_thread, NULL, &attacker_t, NULL);
  
  int i = 0;
#ifdef EXECUTE
  while (i++ < 10)
#else
  while (true)
#endif
    /*@ invariant [_]public_invar(auth_enc_pub) &*&
                  !bad(sender) && !bad(receiver) &*&
                  havege_state_initialized(&havege_state) &*&
                  principal(sender, ?count) &*& principal(receiver, _);
    @*/
  {
    char* key;
    int temp;
    
    key = malloc(KEY_SIZE);
    if (key == 0) abort();
    //@ close random_request(sender, 0, true);
    //@ open principal(sender, _);
    if (havege_random(&havege_state, key, KEY_SIZE) != 0) abort();
    //@ assume (shared_with(sender, count + 1) == receiver);
    //@ assert cryptogram(key, KEY_SIZE, ?cs_key, ?cg_key);
    //@ assert cg_key == cg_symmetric_key(sender, count + 1);
    {
      pthread_t s_thread, r_thread;

      struct auth_enc_args s_args;
      struct auth_enc_args r_args;
      char s_message[MSG_LEN];
      char r_message[MAX_SIZE];
    
      memset(s_message, 0, MSG_LEN);
      //@ assert chars(s_message, MSG_LEN, ?msg_cs);
      //@ public_chars(s_message, MSG_LEN);
      //@ chars_to_secret_crypto_chars(s_message, MSG_LEN);
      //@ assert crypto_chars(secret, s_message, MSG_LEN, ?msg_ccs);
      //@ s_args.sender = sender;
      //@ s_args.receiver = receiver;
      s_args.key = key;
      s_args.msg = s_message;
      
      //@ assume (send(sender, receiver, msg_ccs) == true);
      //@ r_args.sender = sender;
      //@ r_args.receiver = receiver;
      r_args.key = key;
      r_args.msg = r_message;
      
      //@ close principal(sender, _);
      //@ close pthread_run_pre(sender_t)(&s_args, ?s_data);
      //@ close pthread_run_pre(receiver_t)(&r_args, ?r_data);
      pthread_create(&r_thread, NULL, &receiver_t, &r_args);
      pthread_create(&s_thread, NULL, &sender_t, &s_args);
      
      pthread_join(s_thread, NULL);
      //@ open pthread_run_post(sender_t)(&s_args, s_data);
      pthread_join(r_thread, NULL);
      //@ open pthread_run_post(receiver_t)(&r_args, r_data);  
      //@ open [1/2]cryptogram(key, KEY_SIZE, cs_key, _);
      //@ open [1/2]cryptogram(key, KEY_SIZE, cs_key, _);

      if (r_args.length != MSG_LEN)
        abort();
#ifdef EXECUTE
      if (memcmp(s_message, r_message, MSG_LEN) != 0)
        abort();
#endif
      //@ public_crypto_chars(s_message, MSG_LEN);
      zeroize(r_message, r_args.length);
    }
    //@ assert malloc_block(key, KEY_SIZE);
    zeroize(key, KEY_SIZE);
    free((void*) key);
    
    printf(" |%i| ", i);
  }
#ifdef EXECUTE
  printf("\n\n\t\tDone\n");
  return 0;
#endif
}

