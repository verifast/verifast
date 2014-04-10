#include "nsl.h"

#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>

/*@
predicate_family_instance pthread_run_pre(attacker_t)(void *data, any info) = 
    exists(nsl_pub) &*& [_]world(nsl_pub) &*&
    attacker_proof_obligations(nsl_pub) &*&
    initial_principals() &*& !bad(0) &*&
    info == nil;
@*/

void *attacker_t(void* _unused) //@ : pthread_run_joinable
  //@ requires pthread_run_pre(attacker_t)(_unused, _);
  //@ ensures false;
{
  //@ open pthread_run_pre(attacker_t)(_unused, _);
  attacker();
  return 0;
}

struct nsl_args
{
  int sender;
  int receiver;
  struct item *key2;
  struct item *key1;
};

/*@
predicate_family_instance pthread_run_pre(receiver_t)(void *data, any info) = 
  [_]world(nsl_pub) &*&
  nsl_args_receiver(data, ?receiver) &*&
  nsl_args_key1(data, ?key_KB_PRIV) &*&
  !bad(receiver) &*&
  generated_nonces(receiver, _) &*&
  key_item(key_KB_PRIV, receiver, ?id, private_key, int_pair(0, 0)) &*&
  info == cons(receiver, nil);
predicate_family_instance pthread_run_post(receiver_t)(void *data, any info) = 
  [_]world(nsl_pub) &*&
  nsl_args_receiver(data, ?receiver) &*&
  nsl_args_key1(data, ?key_KB_PRIV) &*&
  generated_nonces(receiver, _) &*&
  info == cons(receiver, nil);
@*/

void *receiver_t(void* data) //@ : pthread_run_joinable
  //@ requires pthread_run_pre(receiver_t)(data, ?x);
  //@ ensures pthread_run_post(receiver_t)(data, x)  &*& result == 0;
{
  struct nsl_args *args = data;
  //@ open pthread_run_pre(receiver_t)(data, _);
  receiver(args->receiver, args->key1);
  key_free(args->key1);
  //@ close pthread_run_post(receiver_t)(data, _);
  return 0;
}

/*@
predicate_family_instance pthread_run_pre(sender_t)(void *data, any info) = 
  [_]world(nsl_pub) &*&
  nsl_args_sender(data, ?sender) &*&
  nsl_args_receiver(data, ?receiver) &*&
  nsl_args_key1(data, ?key_KA_PRIV) &*&
  nsl_args_key2(data, ?key_KB_PUB) &*&
  !bad(0) &*& !bad(sender) &*& !bad(receiver) &*&
  generated_nonces(sender, _) &*&
  key_item(key_KA_PRIV, sender, 0, private_key, int_pair(0, 0)) &*&
  key_item(key_KB_PUB, receiver, 0, public_key, int_pair(0, 0)) &*&
  info == cons(sender, nil);
predicate_family_instance pthread_run_post(sender_t)(void *data, any info) = 
  [_]world(nsl_pub) &*&
  nsl_args_sender(data, ?sender) &*&
  nsl_args_receiver(data, ?receiver) &*&
  nsl_args_key1(data, ?key_KA_PRIV) &*&
  nsl_args_key2(data, ?key_KB_PUB) &*&
  generated_nonces(sender, _) &*&
  info == cons(sender, nil);
@*/

void *sender_t(void* data) //@ : pthread_run_joinable
  //@ requires pthread_run_pre(sender_t)(data, ?x);
  //@ ensures pthread_run_post(sender_t)(data, x) &*& result == 0;
{
  struct nsl_args *args = data;
  //@ open pthread_run_pre(sender_t)(data, _);
  sender(args->sender, args->receiver, args->key1, args->key2);
  key_free(args->key1);
  key_free(args->key2);
  //@ close pthread_run_post(sender_t)(data, _);
  return 0;
}

int main() //@ : main
  //@ requires true;
  //@ ensures true;
{
  struct item *key;
  struct keypair *keypair;

  printf("\n\tExecuting \"nsl protocol\" ... ");
  //@ close exists(nsl_pub);
  init_crypto_lib();
  //@ init_protocol();
  
  //@ open initial_principals();
  int sendr = create_principal(&key, &keypair);
  key_free(key);
  struct item *KA_PRIV = keypair_get_private_key(keypair);
  struct item *KA_PUBL = keypair_get_public_key(keypair);
  int receiver = create_principal(&key, &keypair);
  struct item *KB_PRIV = keypair_get_private_key(keypair);
  struct item *KB_PUBL = keypair_get_public_key(keypair);
  key_free(key);
  //@ close initial_principals();
  
  //@ assume (!bad(sendr) && !bad(receiver));
  void *null = (void *) 0;
  
  {
    pthread_t a_thread;
    //@ PACK_ATTACKER_PROOF_OBLIGATIONS(nsl)
    //@ close attacker_proof_obligations(nsl_pub);
    //@ leak  world(nsl_pub);
    //@ close pthread_run_pre(attacker_t)(null, _);
    pthread_create(&a_thread, null, &attacker_t, null);  
  }
  
  int i = 0;
#ifdef EXECUTE
  while (i++ < 10)
#else
  while (true)
#endif
    /*@ invariant [_]world(nsl_pub) &*&
                  generated_nonces(sendr, _) &*&
                  generated_nonces(receiver, _) &*&
                  key_item(KA_PRIV, sendr, 0, private_key, int_pair(0, 0)) &*&
                  key_item(KB_PRIV, receiver, 0, private_key, int_pair(0, 0)) &*&
                  key_item(KB_PUBL, receiver, 0, public_key, int_pair(0, 0));
    @*/
  { 
    pthread_t s_thread, r_thread;
    struct nsl_args s_args, r_args;
    { 
      r_args.receiver = receiver;
      r_args.key1 = key_clone(KB_PRIV);
      //@ close pthread_run_pre(receiver_t)(&r_args, cons(receiver, nil));
      pthread_create(&r_thread, null, &receiver_t, &r_args);
      
      s_args.sender = sendr;
      s_args.receiver = receiver;
      s_args.key1 = key_clone(KA_PRIV);
      s_args.key2 = key_clone(KB_PUBL);
      //@ close pthread_run_pre(sender_t)(&s_args, cons(sendr, nil));
      pthread_create(&s_thread, null, &sender_t, &s_args); 
    }
    
    {
      pthread_join(s_thread, null);
      //@ open pthread_run_post(sender_t)(&s_args, _);
      pthread_join(r_thread, null);
      //@ open pthread_run_post(receiver_t)(&r_args, _);
    }
  }
  
  printf("Done\n");
}
