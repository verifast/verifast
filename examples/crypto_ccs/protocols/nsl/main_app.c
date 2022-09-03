#include "nsl.h"

#include "../general.h"

//@ ATTACKER_PRE(nsl)

void *attacker_t(void* data) //@ : pthread_run_joinable
  //@ requires pthread_run_pre(attacker_t)(data, ?info);
  //@ ensures  false;
{
  while(true)
    //@ invariant pthread_run_pre(attacker_t)(data, info);
  {
    //@ open pthread_run_pre(attacker_t)(data, info);
    //@ assert principal(?attacker, _);
    //@ close nsl_proof_pred();
    attacker();
    //@ open nsl_proof_pred();
    //@ open exists(_);
    //@ close exists(attacker);
    //@ close pthread_run_pre(attacker_t)(data, info);
  }
}

struct nsl_args
{
  int sender;
  int receiver;
  
  char* s_key;
  char* r_key;
  char* s_nonce;
  char* r_nonce;
};

/*@

predicate_family_instance pthread_run_pre(sender_t)(void *data, any info) =
  [_]public_invar(nsl_pub) &*&
  [_]decryption_key_classifier(nsl_public_key) &*&
  nsl_args_sender(data, ?sender) &*&
  nsl_args_receiver(data, ?receiver) &*&
  nsl_args_s_key(data, ?s_key) &*&
  nsl_args_r_key(data, ?r_key) &*&
  nsl_args_s_nonce(data, ?s_nonce) &*&
  nsl_args_r_nonce(data, ?r_nonce) &*&
  principal(sender, _) &*&
  [1/2]cryptogram(s_key, 8 * KEY_SIZE, ?s_key_ccs, ?s_key_cg) &*&
    s_key_cg == cg_rsa_private_key(sender, ?s_id) &*&
  [1/2]cryptogram(r_key, 8 * KEY_SIZE, ?r_key_ccs, ?r_key_cg) &*&
    r_key_cg == cg_rsa_public_key(receiver, ?r_id) &*&
  chars_(s_nonce, NONCE_SIZE, _) &*&
  chars_(r_nonce, NONCE_SIZE, _) &*&
  info == IV(sender, IV(receiver, PV(s_key, CCL(s_key_ccs, IV(s_id,
             PV(r_key, CCL(r_key_ccs, IV(r_id, PV(s_nonce, PV(r_nonce, nil))))))))));

predicate_family_instance pthread_run_post(sender_t)(void *data, any info) =
  nsl_args_sender(data, ?sender) &*&
  nsl_args_receiver(data, ?receiver) &*&
  nsl_args_s_key(data, ?s_key) &*&
  nsl_args_r_key(data, ?r_key) &*&
  nsl_args_s_nonce(data, ?s_nonce) &*&
  nsl_args_r_nonce(data, ?r_nonce) &*&
  principal(sender, _) &*&
  [1/2]cryptogram(s_key, 8 * KEY_SIZE, ?s_key_ccs, ?s_key_cg) &*&
    s_key_cg == cg_rsa_private_key(sender, ?s_id) &*&
  [1/2]cryptogram(r_key, 8 * KEY_SIZE, ?r_key_ccs, ?r_key_cg) &*&
    r_key_cg == cg_rsa_public_key(receiver, ?r_id) &*&
  cryptogram(s_nonce, NONCE_SIZE, _, ?s_nonce_cg) &*&
  (
    col || bad(sender) || bad(receiver) ?
      chars(r_nonce, NONCE_SIZE, _)
    :
      cryptogram(r_nonce, NONCE_SIZE, _, ?r_nonce_cg) &*&
      r_nonce_cg == cg_nonce(receiver, _)
  ) &*&
  info == cons(int_value(sender), 
            cons(int_value(receiver), 
              cons(pointer_value(s_key),
                CCL(s_key_ccs,
                  cons(int_value(s_id),
                    cons(pointer_value(r_key),
                      CCL(r_key_ccs,
                        cons(int_value(r_id),
                          cons(pointer_value(s_nonce),
                            cons(pointer_value(r_nonce),
                                 nil))))))))));
@*/

void *sender_t(void* data) //@ : pthread_run_joinable
  //@ requires pthread_run_pre(sender_t)(data, ?x);
  //@ ensures pthread_run_post(sender_t)(data, x) &*& result == 0;
{
  struct nsl_args *args = data;
  //@ open pthread_run_pre(sender_t)(data, _);
  sender(args->sender, args->receiver, args->s_key, args->r_key,
         args->s_nonce, args->r_nonce);
  //@ close pthread_run_post(sender_t)(data, _);
  return 0;
}

/*@

predicate_family_instance pthread_run_pre(receiver_t)(void *data, any info) =
  [_]public_invar(nsl_pub) &*&
  [_]decryption_key_classifier(nsl_public_key) &*&
  nsl_args_sender(data, ?sender) &*&
  nsl_args_receiver(data, ?receiver) &*&
  nsl_args_s_key(data, ?s_key) &*&
  nsl_args_r_key(data, ?r_key) &*&
  nsl_args_s_nonce(data, ?s_nonce) &*&
  nsl_args_r_nonce(data, ?r_nonce) &*&
  principal(receiver, _) &*&
  [1/2]cryptogram(s_key, 8 * KEY_SIZE, ?s_key_ccs, ?s_key_cg) &*&
    s_key_cg == cg_rsa_public_key(sender, ?s_id) &*&
  [1/2]cryptogram(r_key, 8 * KEY_SIZE, ?r_key_ccs, ?r_key_cg) &*&
    r_key_cg == cg_rsa_private_key(receiver, ?r_id) &*&
  chars_(s_nonce, NONCE_SIZE, _) &*&
  chars_(r_nonce, NONCE_SIZE, _) &*&
  info == cons(int_value(sender), 
            cons(int_value(receiver), 
              cons(pointer_value(s_key),
                CCL(s_key_ccs,
                  cons(int_value(s_id),
                    cons(pointer_value(r_key),
                      CCL(r_key_ccs,
                        cons(int_value(r_id),
                          cons(pointer_value(s_nonce),
                            cons(pointer_value(r_nonce),
                                 nil))))))))));
                         
predicate_family_instance pthread_run_post(receiver_t)(void *data, any info) =
  nsl_args_sender(data, ?sender) &*&
  nsl_args_receiver(data, ?receiver) &*&
  nsl_args_s_key(data, ?s_key) &*&
  nsl_args_r_key(data, ?r_key) &*&
  nsl_args_s_nonce(data, ?s_nonce) &*&
  nsl_args_r_nonce(data, ?r_nonce) &*&
  principal(receiver, _) &*&
  [1/2]cryptogram(s_key, 8 * KEY_SIZE, ?s_key_ccs, ?s_key_cg) &*&
    s_key_cg == cg_rsa_public_key(sender, ?s_id) &*&
  [1/2]cryptogram(r_key, 8 * KEY_SIZE, ?r_key_ccs, ?r_key_cg) &*&
    r_key_cg == cg_rsa_private_key(receiver, ?r_id) &*&
  cryptogram(r_nonce, NONCE_SIZE, _, ?r_nonce_cg) &*&
    r_nonce_cg == cg_nonce(receiver, _) &*&
  (
    col || bad(sender) || bad(receiver) ?
      chars(s_nonce, NONCE_SIZE, _)
    :
      cryptogram(s_nonce, NONCE_SIZE, ?s_nonce_cs, ?s_nonce_cg) &*&
      s_nonce_cg == cg_nonce(sender, _)
  ) &*&
  info == cons(int_value(sender), 
            cons(int_value(receiver), 
              cons(pointer_value(s_key),
                CCL(s_key_ccs,
                  cons(int_value(s_id),
                    cons(pointer_value(r_key),
                      CCL(r_key_ccs,
                        cons(int_value(r_id),
                          cons(pointer_value(s_nonce),
                            cons(pointer_value(r_nonce),
                                 nil))))))))));
@*/

void *receiver_t(void* data) //@ : pthread_run_joinable
  //@ requires pthread_run_pre(receiver_t)(data, ?x);
  //@ ensures pthread_run_post(receiver_t)(data, x) &*& result == 0;
{
  struct nsl_args *args = data;
  //@ open pthread_run_pre(receiver_t)(data, _);
  receiver(args->sender, args->receiver, args->s_key, args->r_key,
           args->s_nonce, args->r_nonce);
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
  pthread_t a_thread;
  havege_state havege_state;
  
  printf("\n\tExecuting \"");
  printf("nsl protocol");
  printf("\" ... \n\n");
  
  //@ PROTOCOL_INIT(nsl)
  //@ int sender = principal_create();
  //@ assert sender == 1;
  //@ int receiver = principal_create();
  //@ assert receiver == 2;
  
  //@ int attacker = principal_create();
  //@ assume (bad(attacker));
  //@ close havege_state(&havege_state);
  havege_init(&havege_state);
  //@ close exists(attacker);
  //@ assume (bad(attacker));
  //@ close pthread_run_pre(attacker_t)(NULL, some(attacker));
  pthread_create(&a_thread, NULL, &attacker_t, NULL);
  
  int i = 0;
#ifdef EXECUTE
  while (i++ < 10)
#else
  while (true)
#endif
    /*@ invariant [_]public_invar(nsl_pub) &*&
                  [_]decryption_key_classifier(nsl_public_key) &*&
                  havege_state_initialized(&havege_state) &*&
                  principal(sender, ?s_count) &*&
                  principal(receiver, ?r_count);
    @*/
  {
    pk_context s_context;
    char s_priv_key[4096];
    char s_pub_key[4096];
    pk_context r_context;
    char r_priv_key[4096];
    char r_pub_key[4096];
    
    //@ close random_state_predicate(havege_state_initialized);
    /*@ produce_function_pointer_chunk random_function(random_stub_main)
                     (havege_state_initialized)(state, out, len) { call(); } @*/
                     
    // sender keys
    //@ close pk_context(&s_context);
    pk_init(&s_context);
    if (pk_init_ctx(&s_context, pk_info_from_type(MBEDTLS_PK_RSA)) != 0)
      abort();
    //@ close rsa_key_request(sender, 0);
    //@ open principal(sender, _);
    if (rsa_gen_key(s_context.pk_ctx, random_stub_main, (void*) &havege_state, 
                    (unsigned int) 8 * KEY_SIZE, 65537) != 0)
      abort();
    //@ close principal(sender, _);
    if (pk_write_pubkey_pem(&s_context, s_pub_key, 
                            (unsigned int) 8 * KEY_SIZE) != 0) abort();
    if (pk_write_key_pem(&s_context, s_priv_key,
                         (unsigned int) 8 * KEY_SIZE) != 0) abort();
    //@ assert cryptogram(s_priv_key, 8 * KEY_SIZE, ?ccs_s_priv_key, ?cg_s_priv_key);
    //@ assert cryptogram(s_pub_key, 8 * KEY_SIZE, ?ccs_s_pub_key, ?cg_s_pub_key);
    //@ assert cg_s_priv_key == cg_rsa_private_key(sender, s_count + 1);
    //@ assert cg_s_pub_key == cg_rsa_public_key(sender, s_count + 1);
    //@ pk_release_context_with_keys(&s_context);
    pk_free(&s_context);
    //@ open pk_context(&s_context);
    
    // receiver keys
    //@ close pk_context(&r_context);
    pk_init(&r_context);
    if (pk_init_ctx(&r_context, pk_info_from_type(MBEDTLS_PK_RSA)) != 0)
      abort();
    //@ close rsa_key_request(receiver, 0);
    //@ open principal(receiver, _);
    if (rsa_gen_key(r_context.pk_ctx, random_stub_main, (void*) &havege_state, 
                    (unsigned int) 8 * KEY_SIZE, 65537) != 0)
      abort();
    //@ close principal(receiver, _);
    if (pk_write_pubkey_pem(&r_context, r_pub_key, 
                            (unsigned int) 8 * KEY_SIZE) != 0) abort();
    if (pk_write_key_pem(&r_context, r_priv_key, 
                         (unsigned int) 8 * KEY_SIZE) != 0) abort();
    //@ assert cryptogram(r_priv_key, 8 * KEY_SIZE, ?ccs_r_priv_key, ?cg_r_priv_key);
    //@ assert cryptogram(r_pub_key, 8 * KEY_SIZE, ?ccs_r_pub_key, ?cg_r_pub_key);
    //@ assert cg_r_priv_key == cg_rsa_private_key(receiver, r_count + 1);
    //@ assert cg_r_pub_key == cg_rsa_public_key(receiver, r_count + 1);
    //@ pk_release_context_with_keys(&r_context);
    pk_free(&r_context);
    //@ open pk_context(&r_context);
    
    //@ open random_state_predicate(havege_state_initialized);
    {
      pthread_t s_thread, r_thread;

      struct nsl_args s_args;
      struct nsl_args r_args;
      char s_s_nonce[NONCE_SIZE];
      char s_r_nonce[NONCE_SIZE];
      char r_s_nonce[NONCE_SIZE];
      char r_r_nonce[NONCE_SIZE];
    
      s_args.sender = 1;
      s_args.receiver = 2;
      s_args.s_key = s_priv_key;
      s_args.r_key = r_pub_key;
      s_args.s_nonce = s_s_nonce;
      s_args.r_nonce = s_r_nonce;
      
      r_args.sender = 1;
      r_args.receiver = 2;
      r_args.s_key = s_pub_key;
      r_args.r_key = r_priv_key;
      r_args.s_nonce = r_s_nonce;
      r_args.r_nonce = r_r_nonce;
      
      //@ close pthread_run_pre(sender_t)(&s_args, ?s_data);
      pthread_create(&s_thread, NULL, &sender_t, &s_args);
      //@ close pthread_run_pre(receiver_t)(&r_args, ?r_data);
      pthread_create(&r_thread, NULL, &receiver_t, &r_args);
      
      pthread_join(s_thread, NULL);
      //@ open pthread_run_post(sender_t)(&s_args, s_data);
      pthread_join(r_thread, NULL);
      //@ open pthread_run_post(receiver_t)(&r_args, r_data);
    
#ifdef EXECUTE
      //Nonces are secret, therefor this check can not be verified
      if (memcmp(s_s_nonce, r_s_nonce, NONCE_SIZE) != 0)
        abort();
      if (memcmp(s_r_nonce, r_r_nonce, NONCE_SIZE) != 0)
        abort();
#endif
        
      //@ open cryptogram(s_s_nonce, NONCE_SIZE, ?ccs_s_s_nonce, _);
      zeroize(s_s_nonce, NONCE_SIZE);
      /*@ if (!col && !bad(sender) && !bad(receiver)) 
            open cryptogram(s_r_nonce, NONCE_SIZE, _, _); 
          else
            chars_to_crypto_chars(s_r_nonce, NONCE_SIZE); @*/
      zeroize(s_r_nonce, NONCE_SIZE);
      /*@ if (!col && !bad(sender) && !bad(receiver)) 
            open cryptogram(r_s_nonce, NONCE_SIZE, _, _); 
          else
            chars_to_crypto_chars(r_s_nonce, NONCE_SIZE); @*/
      zeroize(r_s_nonce, NONCE_SIZE);
      //@ open cryptogram(r_r_nonce, NONCE_SIZE, ?ccs_r_r_nonce, _);
      zeroize(r_r_nonce, NONCE_SIZE);                
      printf(" |%i| ", i);
    }
    //@ open [1/2]cryptogram(s_priv_key, 8 * KEY_SIZE, ccs_s_priv_key, _);
    //@ open [1/2]cryptogram(s_priv_key, 8 * KEY_SIZE, ccs_s_priv_key, _);
    zeroize(s_priv_key, 8 * KEY_SIZE);
    //@ close nsl_pub(cg_s_pub_key);
    //@ leak nsl_pub(cg_s_pub_key);
    //@ open [1/2]cryptogram(s_pub_key, 8 * KEY_SIZE, ccs_s_pub_key, cg_s_pub_key);
    //@ open [1/2]cryptogram(s_pub_key, 8 * KEY_SIZE, ccs_s_pub_key, cg_s_pub_key);
    //@ close cryptogram(s_pub_key, 8 * KEY_SIZE, ccs_s_pub_key, cg_s_pub_key);
    //@ public_cryptogram(s_pub_key, cg_s_pub_key);
    //@ assert chars(s_pub_key, 8 * KEY_SIZE, _);
    
    //@ open [1/2]cryptogram(r_priv_key, 8 * KEY_SIZE, ccs_r_priv_key, _);
    //@ open [1/2]cryptogram(r_priv_key, 8 * KEY_SIZE, ccs_r_priv_key, _);
    zeroize(r_priv_key, 8 * KEY_SIZE);
    //@ close nsl_pub(cg_r_pub_key);
    //@ leak nsl_pub(cg_r_pub_key);
    //@ open [1/2]cryptogram(r_pub_key, 8 * KEY_SIZE, ccs_r_pub_key, cg_r_pub_key);
    //@ open [1/2]cryptogram(r_pub_key, 8 * KEY_SIZE, ccs_r_pub_key, cg_r_pub_key);
    //@ close cryptogram(r_pub_key, 8 * KEY_SIZE, ccs_r_pub_key, cg_r_pub_key);
    //@ public_cryptogram(r_pub_key, cg_r_pub_key);
    //@ assert chars(r_pub_key, 8 * KEY_SIZE, _);
  }
#ifdef EXECUTE
  printf("\n\n\t\tDone\n");
  return 0;
#endif
}

