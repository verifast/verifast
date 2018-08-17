#include "hmac_then_enc_nested.h"

#include "../general.h"

#define MSG_LEN 64

//@ ATTACKER_PRE(hmac_then_enc_nested)

void *attacker_t(void* data) //@ : pthread_run_joinable
  //@ requires pthread_run_pre(attacker_t)(data, ?info);
  //@ ensures  false;
{
  while(true)
    //@ invariant pthread_run_pre(attacker_t)(data, info);
  {
    //@ open pthread_run_pre(attacker_t)(data, info);
    //@ close hmac_then_enc_nested_proof_pred();
    attacker();
    //@ open hmac_then_enc_nested_proof_pred();
    //@ close pthread_run_pre(attacker_t)(data, info);
  }
   
  return 0;
}

struct hmac_then_enc_nested_args
{
  //@ int sender;
  //@ int receiver;
  
  char* enc_key1;
  char* enc_key2;
  char* hmac_key;
  char* msg;
  
  int length;
};

/*@

predicate_family_instance pthread_run_pre(sender_t)(void *data, any info) =
  [_]public_invar(hmac_then_enc_nested_pub) &*&
  hmac_then_enc_nested_args_sender(data, ?sender) &*&
  hmac_then_enc_nested_args_receiver(data, ?receiver) &*&
  hmac_then_enc_nested_args_enc_key1(data, ?enc_key1) &*&
  hmac_then_enc_nested_args_enc_key2(data, ?enc_key2) &*&
  hmac_then_enc_nested_args_hmac_key(data, ?hmac_key) &*&
  hmac_then_enc_nested_args_msg(data, ?msg) &*&
  principal(sender, _) &*&
  [1/2]cryptogram(enc_key1, KEY_SIZE, ?enc_key_ccs1, ?enc_key_cg1) &*&
    enc_key_cg1 == cg_symmetric_key(sender, ?enc_id1) &*&
    receiver == shared_with(sender, enc_id1) &*&
  [1/2]cryptogram(enc_key2, KEY_SIZE, ?enc_key_ccs2, ?enc_key_cg2) &*&
    enc_key_cg2 == cg_symmetric_key(sender, ?enc_id2) &*&
    receiver == shared_with(sender, enc_id2) &*&
  [1/2]cryptogram(hmac_key, KEY_SIZE, ?hmac_key_ccs, ?hmac_key_cg) &*&
    hmac_key_cg == cg_symmetric_key(sender, ?hmac_id) &*&
    receiver == shared_with(sender, hmac_id) &*&
    cg_info(enc_key_cg1) == hmac_id &*&
    cg_info(enc_key_cg2) == hmac_id &*&
  crypto_chars(secret, msg, MSG_LEN, ?msg_ccs) &*&
  (
    bad(sender) || bad(receiver) ?
      [_]public_ccs(msg_ccs)
    :
      [_]memcmp_region(_, msg_ccs) &*&
      true == send(sender, receiver, msg_ccs) 
  ) &*&
  info == IV(sender, IV(receiver, PV(enc_key1, CCL(enc_key_ccs1, IV(enc_id1,
             PV(enc_key2, CCL(enc_key_ccs2, IV(enc_id2, PV(hmac_key, 
                CCL(hmac_key_ccs, IV(hmac_id, PV(msg, CCL(msg_ccs, nil)))))))))))));

predicate_family_instance pthread_run_post(sender_t)(void *data, any info) =
  [_]public_invar(hmac_then_enc_nested_pub) &*&
  hmac_then_enc_nested_args_sender(data, ?sender) &*&
  hmac_then_enc_nested_args_receiver(data, ?receiver) &*&
  hmac_then_enc_nested_args_enc_key1(data, ?enc_key1) &*&
  hmac_then_enc_nested_args_enc_key2(data, ?enc_key2) &*&
  hmac_then_enc_nested_args_hmac_key(data, ?hmac_key) &*&
  hmac_then_enc_nested_args_msg(data, ?msg) &*& 
  principal(sender, _) &*&
  [1/2]cryptogram(enc_key1, KEY_SIZE, ?enc_key_ccs1, ?enc_key_cg1) &*&
    enc_key_cg1 == cg_symmetric_key(sender, ?enc_id1) &*&
    receiver == shared_with(sender, enc_id1) &*&
  [1/2]cryptogram(enc_key2, KEY_SIZE, ?enc_key_ccs2, ?enc_key_cg2) &*&
    enc_key_cg2 == cg_symmetric_key(sender, ?enc_id2) &*&
    receiver == shared_with(sender, enc_id2) &*&
  [1/2]cryptogram(hmac_key, KEY_SIZE, ?hmac_key_ccs, ?hmac_key_cg) &*&
    hmac_key_cg == cg_symmetric_key(sender, ?hmac_id) &*&
    receiver == shared_with(sender, hmac_id) &*&
  crypto_chars(secret, msg, MSG_LEN, ?msg_ccs) &*&
  info == IV(sender, IV(receiver, PV(enc_key1, CCL(enc_key_ccs1, IV(enc_id1,
             PV(enc_key2, CCL(enc_key_ccs2, IV(enc_id2, PV(hmac_key, 
                CCL(hmac_key_ccs, IV(hmac_id, PV(msg, CCL(msg_ccs, nil)))))))))))));
@*/

void *sender_t(void* data) //@ : pthread_run_joinable
  //@ requires pthread_run_pre(sender_t)(data, ?x);
  //@ ensures pthread_run_post(sender_t)(data, x) &*& result == 0;
{
  struct hmac_then_enc_nested_args *args = data;
  //@ open pthread_run_pre(sender_t)(data, _);
  sender(args->enc_key1, args->enc_key2, args->hmac_key, args->msg, MSG_LEN);
  //@ close pthread_run_post(sender_t)(data, _);
  return 0;
}

/*@

predicate_family_instance pthread_run_pre(receiver_t)(void *data, any info) =
  [_]public_invar(hmac_then_enc_nested_pub) &*&
  [_]decryption_key_classifier(hmac_then_enc_nested_public_key) &*&
  hmac_then_enc_nested_args_sender(data, ?sender) &*&
  hmac_then_enc_nested_args_receiver(data, ?receiver) &*&
  hmac_then_enc_nested_args_enc_key1(data, ?enc_key1) &*&
  hmac_then_enc_nested_args_enc_key2(data, ?enc_key2) &*&
  hmac_then_enc_nested_args_hmac_key(data, ?hmac_key) &*&
  hmac_then_enc_nested_args_msg(data, ?msg) &*&
  hmac_then_enc_nested_args_length(data, _) &*& 
  !bad(sender) && !bad(receiver) &*&
  principal(receiver, _) &*&
  [1/2]cryptogram(enc_key1, KEY_SIZE, ?enc_key_ccs1, ?enc_key_cg1) &*&
    enc_key_cg1 == cg_symmetric_key(sender, ?enc_id1) &*&
    receiver == shared_with(sender, enc_id1) &*&
  [1/2]cryptogram(enc_key2, KEY_SIZE, ?enc_key_ccs2, ?enc_key_cg2) &*&
    enc_key_cg2 == cg_symmetric_key(sender, ?enc_id2) &*&
    receiver == shared_with(sender, enc_id2) &*&
  [1/2]cryptogram(hmac_key, KEY_SIZE, ?hmac_key_ccs, ?hmac_key_cg) &*&
    hmac_key_cg == cg_symmetric_key(sender, ?hmac_id) &*&
    receiver == shared_with(sender, hmac_id) &*&
    cg_info(enc_key_cg1) == hmac_id &*&
    cg_info(enc_key_cg2) == hmac_id &*&
  chars(msg, MAX_SIZE, _) &*&
  info == IV(sender, IV(receiver, PV(enc_key1, CCL(enc_key_ccs1, IV(enc_id1,
             PV(enc_key2, CCL(enc_key_ccs2, IV(enc_id2, PV(hmac_key, 
                CCL(hmac_key_ccs, IV(hmac_id, PV(msg, nil))))))))))));

predicate_family_instance pthread_run_post(receiver_t)(void *data, any info) =
  hmac_then_enc_nested_args_sender(data, ?sender) &*&
  hmac_then_enc_nested_args_receiver(data, ?receiver) &*&
  hmac_then_enc_nested_args_enc_key1(data, ?enc_key1) &*&
  hmac_then_enc_nested_args_enc_key2(data, ?enc_key2) &*&
  hmac_then_enc_nested_args_hmac_key(data, ?hmac_key) &*&
  hmac_then_enc_nested_args_msg(data, ?msg) &*&
  hmac_then_enc_nested_args_length(data, ?length) &*& 
  principal(receiver, _) &*&
  [1/2]cryptogram(enc_key1, KEY_SIZE, ?enc_key_ccs1, ?enc_key_cg1) &*&
    enc_key_cg1 == cg_symmetric_key(sender, ?enc_id1) &*&
    receiver == shared_with(sender, enc_id1) &*&
  [1/2]cryptogram(enc_key2, KEY_SIZE, ?enc_key_ccs2, ?enc_key_cg2) &*&
    enc_key_cg2 == cg_symmetric_key(sender, ?enc_id2) &*&
    receiver == shared_with(sender, enc_id2) &*&
  [1/2]cryptogram(hmac_key, KEY_SIZE, ?hmac_key_ccs, ?hmac_key_cg) &*&
    hmac_key_cg == cg_symmetric_key(sender, ?hmac_id) &*&
    receiver == shared_with(sender, hmac_id) &*&
  crypto_chars(secret, msg, length, ?msg_ccs) &*&
  chars(msg + length, MAX_SIZE - length, _) &*&
  col || send(sender, receiver, msg_ccs) &*&
  info == IV(sender, IV(receiver, PV(enc_key1, CCL(enc_key_ccs1, IV(enc_id1,
             PV(enc_key2, CCL(enc_key_ccs2, IV(enc_id2, PV(hmac_key, 
                CCL(hmac_key_ccs, IV(hmac_id, PV(msg, nil))))))))))));
@*/

void *receiver_t(void* data) //@ : pthread_run_joinable
  //@ requires pthread_run_pre(receiver_t)(data, ?x);
  //@ ensures pthread_run_post(receiver_t)(data, x) &*& result == 0;
{
  struct hmac_then_enc_nested_args *args = data;
  //@ open pthread_run_pre(receiver_t)(data, _);
  args->length = receiver(args->enc_key1, args->enc_key2, 
                          args->hmac_key, args->msg);
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
  printf("hmac_then_enc_nested protocol");
  printf("\" ... \n\n");
  
  //@ PROTOCOL_INIT(hmac_then_enc_nested)
  //@ int attacker = principal_create();
  //@ int sender = principal_create();
  //@ int receiver = principal_create();
  //@ assume (!bad(sender) && !bad(receiver));
  
  //@ close havege_state(&havege_state);
  havege_init(&havege_state);
  //@ assume (bad(attacker));
  //@ close pthread_run_pre(attacker_t)(NULL, some(attacker));
  pthread_create(&a_thread, NULL, &attacker_t, NULL);
  
  int i = 0;
#ifdef EXECUTE
  while (i++ < 10)
#else
  while (true)
#endif
    /*@ invariant [_]public_invar(hmac_then_enc_nested_pub) &*&
                  [_]decryption_key_classifier(hmac_then_enc_nested_public_key) &*&
                  !bad(sender) && !bad(receiver) &*&
                  havege_state_initialized(&havege_state) &*&
                  principal(sender, ?count) &*& principal(receiver, _);
    @*/
  {
    char* enc_key1;
    char* enc_key2;
    char* hmac_key;
    int temp;
    
    enc_key1 = malloc(KEY_SIZE);
    if (enc_key1 == 0) abort();
    enc_key2 = malloc(KEY_SIZE);
    if (enc_key2 == 0) abort();
    hmac_key = malloc(KEY_SIZE);
    if (hmac_key == 0) abort();
    
    //@ open principal(sender, _);
    //@ close random_request(sender, 0, true);
    if (havege_random(&havege_state, hmac_key, KEY_SIZE) != 0) abort();
    //@ assume (shared_with(sender, count + 1) == receiver);
    //@ assert cryptogram(hmac_key, KEY_SIZE, ?hmac_cs_key, ?hmac_cg_key);
    //@ assert hmac_cg_key == cg_symmetric_key(sender, count + 1);
    
    //@ close random_request(sender, count + 1, true);
    if (havege_random(&havege_state, enc_key1, KEY_SIZE) != 0) abort();
    //@ assume (shared_with(sender, count + 2) == receiver);
    //@ assert cryptogram(enc_key1, KEY_SIZE, ?enc_cs_key1, ?enc_cg_key1);
    //@ assert enc_cg_key1 == cg_symmetric_key(sender, count + 2);
    
    //@ close random_request(sender, count + 1, true);
    if (havege_random(&havege_state, enc_key2, KEY_SIZE) != 0) abort();
    //@ assume (shared_with(sender, count + 3) == receiver);
    //@ assert cryptogram(enc_key2, KEY_SIZE, ?enc_cs_key2, ?enc_cg_key2);
    //@ assert enc_cg_key2 == cg_symmetric_key(sender, count + 3);
    
    {
      pthread_t s_thread, r_thread;

      struct hmac_then_enc_nested_args s_args;
      struct hmac_then_enc_nested_args r_args;
      char s_message[MSG_LEN];
      char r_message[MAX_SIZE];
    
      //@ assert chars(s_message, MSG_LEN, ?msg_cs);
      //@ public_chars(s_message, MSG_LEN);
      //@ MEMCMP_CCS(cs_to_ccs(msg_cs))
      //@ chars_to_secret_crypto_chars(s_message, MSG_LEN);
      //@ assert crypto_chars(secret, s_message, MSG_LEN, ?msg_ccs);
      //@ s_args.sender = sender;
      //@ s_args.receiver = receiver;
      s_args.enc_key1 = enc_key1;
      s_args.enc_key2 = enc_key2;
      s_args.hmac_key = hmac_key;
      s_args.msg = s_message;
      
      //@ assume (send(sender, receiver, msg_ccs) == true);      
      //@ r_args.sender = sender;
      //@ r_args.receiver = receiver;
      r_args.enc_key1 = enc_key1;
      r_args.enc_key2 = enc_key2;
      r_args.hmac_key = hmac_key;
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
      //@ open [1/2]cryptogram(enc_key1, KEY_SIZE, enc_cs_key1, _);
      //@ open [1/2]cryptogram(enc_key1, KEY_SIZE, enc_cs_key1, _);
      //@ open [1/2]cryptogram(enc_key2, KEY_SIZE, enc_cs_key2, _);
      //@ open [1/2]cryptogram(enc_key2, KEY_SIZE, enc_cs_key2, _);
      //@ open [1/2]cryptogram(hmac_key, KEY_SIZE, hmac_cs_key, _);
      //@ open [1/2]cryptogram(hmac_key, KEY_SIZE, hmac_cs_key, _);

      if (r_args.length != MSG_LEN)
        abort();
#ifdef EXECUTE        
      if (memcmp(s_message, r_message, MSG_LEN) != 0)
        abort();
#endif
      //@ public_crypto_chars(s_message, MSG_LEN);
      zeroize(r_message, r_args.length);
    }
    //@ assert malloc_block(enc_key1, KEY_SIZE);
    zeroize(enc_key1, KEY_SIZE);
    free((void*) enc_key1);
    //@ assert malloc_block(enc_key2, KEY_SIZE);
    zeroize(enc_key2, KEY_SIZE);
    free((void*) enc_key2);
    //@ assert malloc_block(hmac_key, KEY_SIZE);
    zeroize(hmac_key, KEY_SIZE);
    free((void*) hmac_key);
    
    printf(" |%i| ", i);
  }
  
  printf("\n\n\t\tDone\n");
  return 0;
}

