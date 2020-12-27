#include "secure_storage_asym.h"

#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>

//@ import_module symbolic;

struct ss_auth_args
{
  int attacker;
  struct keypair *keypair;
  
  struct item *key;
};

/*@
predicate_family_instance pthread_run_pre(attacker_t)(void *data, any info) =
    [_]world(ss_auth_pub, ss_auth_key_clsfy) &*&
    ss_auth_args_attacker(data, ?attacker) &*&
    true == bad(attacker) &*&
    principal(attacker, _) &*&
    ss_auth_args_keypair(data, ?keypair) &*&    
    keypair(keypair, attacker, _, ?i, ss_auth_pub) &*&
    principals_created(_) &*& info == nil;
@*/

void *attacker_t(void* data) //@ : pthread_run_joinable
  //@ requires pthread_run_pre(attacker_t)(data, ?info);
  //@ ensures false;
{
  //@ open pthread_run_pre(attacker_t)(data, info);
  struct ss_auth_args *args = (void*) data;
  symbolic_attacker(args->attacker, args->keypair);
}

/*@
inductive info =
  | int_value(int v)
  | pointer_value(void* p)
;

predicate_family_instance pthread_run_pre(receiver_t)(void *data, any info) =
  [_]world(ss_auth_pub, ss_auth_key_clsfy) &*&
  ss_auth_args_key(data, ?key) &*&  
  principal(?principal, ?count) &*&  
    item(key, public_key_item(?sender, _), ss_auth_pub) &*&
  info == cons(pointer_value(key),
            cons(int_value(sender), 
                 nil));
predicate_family_instance pthread_run_post(receiver_t)(void *data, any info) =
  ss_auth_args_key(data, ?key) &*& 
  principal(?principal, ?count) &*&   
    item(key, public_key_item(?sender, _), ss_auth_pub) &*&
  info == cons(pointer_value(key),
            cons(int_value(sender), 
                 nil));
@*/

void *receiver_t(void* data) //@ : pthread_run_joinable
  //@ requires pthread_run_pre(receiver_t)(data, ?x);
  //@ ensures pthread_run_post(receiver_t)(data, x) &*& result == 0;
{
  //@ open pthread_run_pre(receiver_t)(data, _);
  struct ss_auth_args *args = (void*) data;
  struct item *i = app_receive(args->key);
  item_free(i);
  //@ close pthread_run_post(receiver_t)(data, _);
  return 0;
}

/*@
predicate_family_instance pthread_run_pre(sender_t)(void *data, any info) =
  [_]world(ss_auth_pub, ss_auth_key_clsfy) &*& 
  ss_auth_args_key(data, ?key) &*&
    item(key, private_key_item(?sender, _), ss_auth_pub) &*&
  principal(?principal, ?count) &*&
  info == cons(pointer_value(key),
            cons(int_value(sender), 
                 nil));
predicate_family_instance pthread_run_post(sender_t)(void *data, any info) =
  ss_auth_args_key(data, ?key) &*&
    item(key, private_key_item(?sender, _), ss_auth_pub) &*&
  principal(?principal, ?count) &*&
  info == cons(pointer_value(key),
            cons(int_value(sender), 
                 nil));
@*/

void *sender_t(void* data) //@ : pthread_run_joinable
  //@ requires pthread_run_pre(sender_t)(data, ?x);
  //@ ensures pthread_run_post(sender_t)(data, x) &*& result == 0;
{
  //@ open pthread_run_pre(sender_t)(data, _);
  struct ss_auth_args *args = (void*) data;
  struct item *key = args->key;
  //@ assert principal(?principal, ?count);
  //@ item n = nonce_item(principal, count + 1, 0);
  //@ close ss_auth_pub(n);
  //@ leak ss_auth_pub(n);
  int i = random_int();
  struct item *mess_authage = create_data_item((void*) &i, (int) sizeof(int));
  //@ chars_to_integer(&i);
  //@ assert item(key, private_key_item(?sender, _), ss_auth_pub);
  //@ item datai = data_item(chars_of_int(i));
  //@ assume (app_send_event(sender, datai));
  //@ assert [_]world(ss_auth_pub, ss_auth_key_clsfy);
  //@ close ss_auth_pub(datai);
  //@ leak ss_auth_pub(datai);
  app_send(key, mess_authage);
  //@ close pthread_run_post(sender_t)(data, _);
  item_free(mess_authage);
  return 0;
}

int main() //@ : main_full(main_app)
  //@ requires module(main_app, true);
  //@ ensures  true;
{
  struct keypair *apair;
  struct keypair *pair;
  struct item *key;
  struct item *pub_key;
  struct item *priv_key;

  printf("\n\tExecuting \""); 
  printf("auth secure_storage");
  printf("protocol");
  printf("\" ... \n\n");
  
  //@ open_module();
  //@ PACK_PROOF_OBLIGATIONS(ss_auth)
  init_crypto_lib();

  int attacker = create_principal(&apair);
  //@ assume (bad(attacker));
  
  int sender = create_principal(&pair);
  pub_key = keypair_get_public_key(pair);
  priv_key = keypair_get_private_key(pair);
  keypair_free(pair);
  int receiver = create_principal(&pair);
  keypair_free(pair);
  
  void *null = (void *) 0;
  //@ leak  world(ss_auth_pub, ss_auth_key_clsfy);
  { 
    pthread_t a_thread;
    struct ss_auth_args *args = malloc(sizeof(struct ss_auth_args));
    if (args == 0) abort();
    args->attacker = attacker;
    args->keypair = apair;  
    //@ close pthread_run_pre(attacker_t)(args, _);
    pthread_create(&a_thread, NULL, &attacker_t, args);
  }

  int i = 0;
#ifdef EXECUTE
  while (i++ < 10)
#else
  while (true)
#endif
    /*@ invariant [_]world(ss_auth_pub, ss_auth_key_clsfy) &*& 
          principal(_, _) &*& principal(_, _) &*&
          item(pub_key, public_key_item(sender, _), ss_auth_pub) &*&
          item(priv_key, private_key_item(sender, _), ss_auth_pub);
    @*/
  {
    pthread_t s_thread, r_thread;
    struct ss_auth_args *args_s = malloc(sizeof(struct ss_auth_args));
    if (args_s == 0) abort();
    struct ss_auth_args *args_r = malloc(sizeof(struct ss_auth_args));
    if (args_r == 0) abort();
    args_s->key = priv_key;
    args_r->key = pub_key;
    
    {
      /*@ close pthread_run_pre(sender_t)(args_s, cons(pointer_value(priv_key),
                                          cons(int_value(sender), nil))); @*/
      pthread_create(&s_thread, null, &sender_t, args_s);
      /*@ close pthread_run_pre(receiver_t)(args_r, cons(pointer_value(pub_key),
                                            cons(int_value(sender), nil))); @*/
      pthread_create(&r_thread, null, &receiver_t, args_r);
    }
    
    {
      pthread_join(r_thread, null);
      //@ open pthread_run_post(receiver_t)(args_r, _);
      pthread_join(s_thread, null);
      //@ open pthread_run_post(sender_t)(args_s, _);
    }
    free(args_s);
    free(args_r);
  }
#ifdef EXECUTE
  //@ close_module();
  //@ leak module(main_app, _);
  printf("Done\n");
#endif
}
