#include "hmac.h"

#include "../general.h"

#define KEY_SIZE 16

//@ ATTACKER_PRE(hmac)

void *attacker_t(void* data) //@ : pthread_run_joinable
  //@ requires pthread_run_pre(attacker_t)(data, ?info);
  //@ ensures  false;
{
  while(true)
    //@ invariant pthread_run_pre(attacker_t)(data, info);
  {
    //@ open pthread_run_pre(attacker_t)(data, info);
    //@ close hmac_proof_pred();
    attacker();
    //@ open hmac_proof_pred();
    //@ close pthread_run_pre(attacker_t)(data, info);
  }
}

struct hmac_args
{
  //@ int sender;
  //@ int receiver;
  
  char* key;
  char* message;
};

/*@

predicate_family_instance pthread_run_pre(sender_t)(void *data, any info) =
  [_]public_invar(hmac_pub) &*&
  hmac_args_sender(data, ?sender) &*&
  hmac_args_receiver(data, ?receiver) &*&
  hmac_args_key(data, ?key) &*&
  hmac_args_message(data, ?msg) &*&
  principal(sender, _) &*&
  [1/2]cryptogram(key, KEY_SIZE, ?key_cs, ?key_cg) &*&
    key_cg == cg_symmetric_key(sender, ?id) &*&
    receiver == shared_with(sender, id) &*&
  chars(msg, MESSAGE_SIZE, ?msg_cs) &*&
    true == send(sender, receiver, msg_cs) &*&
  info == IV(sender, IV(receiver, PV(key, CCL(key_cs, 
             IV(id, PV(msg, CL(msg_cs, nil)))))));

predicate_family_instance pthread_run_post(sender_t)(void *data, any info) =
  hmac_args_sender(data, ?sender) &*&
  hmac_args_receiver(data, ?receiver) &*&
  hmac_args_key(data, ?key) &*&
  hmac_args_message(data, ?msg) &*&
  principal(sender, _) &*&
  [1/2]cryptogram(key, KEY_SIZE, ?key_cs, ?key_cg) &*&
    key_cg == cg_symmetric_key(sender, ?id) &*&
  chars(msg, MESSAGE_SIZE, ?msg_cs) &*&
  info == IV(sender, IV(receiver, PV(key, CCL(key_cs, 
             IV(id, PV(msg, CL(msg_cs, nil)))))));
@*/

void *sender_t(void* data) //@ : pthread_run_joinable
  //@ requires pthread_run_pre(sender_t)(data, ?x);
  //@ ensures pthread_run_post(sender_t)(data, x) &*& result == 0;
{
  struct hmac_args *args = data;
  //@ open pthread_run_pre(sender_t)(data, _);
  sender(args->key, KEY_SIZE, args->message);
  //@ close pthread_run_post(sender_t)(data, _);
  return 0;
}

/*@

predicate_family_instance pthread_run_pre(receiver_t)(void *data, any info) =
  [_]public_invar(hmac_pub) &*&
  hmac_args_sender(data, ?sender) &*&
  hmac_args_receiver(data, ?receiver) &*&
  hmac_args_key(data, ?key) &*&
  hmac_args_message(data, ?msg) &*&
  principal(receiver, _) &*&
  [1/2]cryptogram(key, KEY_SIZE, ?key_cs, ?key_cg) &*&
    key_cg == cg_symmetric_key(sender, ?id) &*&
    receiver == shared_with(sender, id) &*&
  chars_(msg, MESSAGE_SIZE, _) &*&
  info == IV(sender, IV(receiver, PV(key, CCL(key_cs, IV(id, PV(msg, nil))))));
                         
predicate_family_instance pthread_run_post(receiver_t)(void *data, any info) =
  hmac_args_sender(data, ?sender) &*&
  hmac_args_receiver(data, ?receiver) &*&
  hmac_args_key(data, ?key) &*&
  hmac_args_message(data, ?msg) &*&
  principal(receiver, _) &*&
  [1/2]cryptogram(key, KEY_SIZE, ?key_cs, ?key_cg) &*&
    key_cg == cg_symmetric_key(sender, ?id) &*&
  chars(msg, MESSAGE_SIZE, ?msg_cs) &*&
  info == IV(sender, IV(receiver, PV(key, CCL(key_cs, IV(id, PV(msg, nil))))));
  
@*/

void *receiver_t(void* data) //@ : pthread_run_joinable
  //@ requires pthread_run_pre(receiver_t)(data, ?x);
  //@ ensures pthread_run_post(receiver_t)(data, x) &*& result == 0;
{
  struct hmac_args *args = data;
  //@ open pthread_run_pre(receiver_t)(data, _);
  receiver(args->key, KEY_SIZE, args->message);
  //@ assert hmac_args_sender(data, ?sender);
  //@ assert hmac_args_receiver(data, ?receiver);
  //@ assert hmac_args_message(data, ?msg);
  //@ assert chars(msg, MESSAGE_SIZE, ?msg_cs);
  /*@ assert col || bad(sender) || bad(receiver) || 
             send(sender, receiver, msg_cs); @*/
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
  printf("hmac protocol");
  printf("\" ... \n\n");
  
  //@ PROTOCOL_INIT(hmac)
  //@ int attacker = principal_create();
  //@ int sender = principal_create();
  //@ int receiver = principal_create();
  
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
    /*@ invariant [_]public_invar(hmac_pub) &*&
                  havege_state_initialized(&havege_state) &*&
                  principal(sender, ?count) &*& principal(receiver, _);
    @*/
  {
    //@ open principal(sender, _);
    char* key;
    int temp;
    
    //@ close random_request(sender, 0, true);
    key = malloc(KEY_SIZE);
    if (key == 0) abort();
    if (havege_random(&havege_state, key, KEY_SIZE) != 0) abort();
    //@ assume (shared_with(sender, count + 1) == receiver);
    //@ assert cryptogram(key, KEY_SIZE, ?cs_key, ?cg_key);
    //@ assert cg_key == cg_symmetric_key(sender, count + 1);
    {
      pthread_t s_thread, r_thread;

      struct hmac_args s_args;
      struct hmac_args r_args;
      char s_message[MESSAGE_SIZE];
      char r_message[MESSAGE_SIZE];
      
      //@ close random_request(sender, 0, false);
      if (havege_random(&havege_state, s_message, MESSAGE_SIZE) != 0) abort();
      //@ assert cryptogram(s_message, MESSAGE_SIZE, _, ?cg);
      //@ close hmac_pub(cg);
      //@ leak hmac_pub(cg);
      //@ public_cryptogram(s_message, cg);
      //@ assert chars(s_message, MESSAGE_SIZE, ?cs);
    
      //@ s_args.sender = sender;
      //@ s_args.receiver = receiver;
      s_args.key = key;
      s_args.message = s_message;
      
      //@ assume (send(sender, receiver, cs) == true);      
      //@ r_args.sender = sender;
      //@ r_args.receiver = receiver;
      r_args.key = key;
      r_args.message = r_message;
      
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
      
      //@ chars_to_crypto_chars(r_message, MESSAGE_SIZE);
      //@ chars_to_crypto_chars(s_message, MESSAGE_SIZE);
      //@ open principal(sender, _);
      //@ MEMCMP_PUB(s_message)
      //@ MEMCMP_PUB(r_message)
      if (crypto_memcmp(s_message, r_message, MESSAGE_SIZE) != 0)
        abort();
      //@ close principal(sender, _);
      printf(" |%i| ", i);
      //@ crypto_chars_to_chars(r_message, MESSAGE_SIZE);
      //@ crypto_chars_to_chars(s_message, MESSAGE_SIZE);
    }
    //@ assert malloc_block(key, KEY_SIZE);
    zeroize(key, KEY_SIZE);
    free((void*) key);
  }
#ifdef EXECUTE
  printf("\n\n\t\tDone\n");
  return 0;
#endif
}

