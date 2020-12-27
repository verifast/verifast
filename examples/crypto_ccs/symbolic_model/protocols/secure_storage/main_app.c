#include "secure_storage.h"

#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>

//@ import_module symbolic;

struct ss_args
{
  int attacker;
  struct keypair *keypair;
  
  struct item *key;
};

/*@
predicate_family_instance pthread_run_pre(attacker_t)(void *data, any info) =
    exists(ss_pub) &*& [_]world(ss_pub, ss_key_clsfy) &*&
    ss_args_attacker(data, ?attacker) &*&
    true == bad(attacker) &*&
    principal(attacker, _) &*&
    ss_args_keypair(data, ?keypair) &*&    
    keypair(keypair, attacker, _, ?i, ss_pub) &*&
    principals_created(_) &*& info == nil;
@*/

void *attacker_t(void* data) //@ : pthread_run_joinable
  //@ requires pthread_run_pre(attacker_t)(data, ?info);
  //@ ensures false;
{
  //@ open pthread_run_pre(attacker_t)(data, info);
  struct ss_args *args = (void*) data;
  symbolic_attacker(args->attacker, args->keypair);
}

/*@
inductive info =
  | int_value(int v)
  | pointer_value(void* p)
;

predicate_family_instance pthread_run_pre(receiver_t)(void *data, any info) =
  [_]world(ss_pub, ss_key_clsfy) &*&
  ss_args_key(data, ?key) &*&    
    item(key, symmetric_key_item(?sender, _), ss_pub) &*&
  principal(sender, _) &*&
  info == cons(pointer_value(key),
            cons(int_value(sender), 
                 nil));
predicate_family_instance pthread_run_post(receiver_t)(void *data, any info) =
  ss_args_key(data, ?key) &*&    
    item(key, symmetric_key_item(?sender, _), ss_pub) &*&
  principal(sender, _) &*&
  info == cons(pointer_value(key),
            cons(int_value(sender), 
                 nil));
@*/

void *receiver_t(void* data) //@ : pthread_run_joinable
  //@ requires pthread_run_pre(receiver_t)(data, ?x);
  //@ ensures pthread_run_post(receiver_t)(data, x) &*& result == 0;
{
  //@ open pthread_run_pre(receiver_t)(data, _);
  struct ss_args *args = (void*) data;
  struct item *i = app_receive(args->key);
  item_free(i);
  //@ close pthread_run_post(receiver_t)(data, _);
  return 0;
}

/*@
predicate_family_instance pthread_run_pre(sender_t)(void *data, any info) =
  [_]world(ss_pub, ss_key_clsfy) &*& 
  ss_args_key(data, ?key) &*&
    item(key, symmetric_key_item(?sender, _), ss_pub) &*&
  principal(?receiver, _) &*&
  info == cons(pointer_value(key),
            cons(int_value(sender), 
              cons(int_value(receiver), 
                   nil)));
predicate_family_instance pthread_run_post(sender_t)(void *data, any info) =
  ss_args_key(data, ?key) &*&
    item(key, symmetric_key_item(?sender, _), ss_pub) &*&
  principal(?receiver, _) &*&
  info == cons(pointer_value(key),
            cons(int_value(sender), 
              cons(int_value(receiver), 
                   nil)));
@*/

void *sender_t(void* data) //@ : pthread_run_joinable
  //@ requires pthread_run_pre(sender_t)(data, ?x);
  //@ ensures pthread_run_post(sender_t)(data, x) &*& result == 0;
{
  //@ open pthread_run_pre(sender_t)(data, _);
  struct ss_args *args = (void*) data;
  struct item *key = args->key;
  //@ assert principal(?p, ?c);
  //@ item nonce = nonce_item(p, c + 1, 0);
  //@ close ss_pub(nonce);
  //@ leak ss_pub(nonce);
  int i = random_int();
  struct item *message = create_data_item_from_int(i);
  //@ assert item(key, symmetric_key_item(?sender, _), ss_pub);
  //@ item datai = data_item(chars_of_int(i));
  //@ assume (app_send_event(sender, datai));
  //@ assert [_]world(ss_pub, ss_key_clsfy);
  //@ close ss_pub(datai);
  //@ leak ss_pub(datai);
  app_send(key, message);
  //@ close pthread_run_post(sender_t)(data, _);
  item_free(message);
  return 0;
}

int main() //@ : main_full(main_app)
  //@ requires module(main_app, true);
  //@ ensures  true;
{
  struct keypair* apair;
  struct keypair* spair;
  struct keypair* rpair;
  struct item *key;
  struct item *s_key;
  struct item *r_key;
  
  printf("\n\tExecuting \""); 
  printf("secure_storage ");
  printf("protocol");
  printf("\" ... \n\n");
  
  //@ open_module();
  //@ PACK_PROOF_OBLIGATIONS(ss)
  init_crypto_lib();

  int attacker = create_principal(&apair);
  //@ assume (bad(attacker));
  int sender = create_principal(&spair);
  int receiver = create_principal(&rpair);
  keypair_free(spair);
  keypair_free(rpair);
  //@ close key_request(sender, int_pair(0, 0));
  s_key = create_symmetric_key();
  r_key = item_clone(s_key);
  //@ leak  world(ss_pub, ss_key_clsfy);
  
  void *null = (void *) 0;

  { 
    pthread_t a_thread;
    struct ss_args *args = malloc(sizeof(struct ss_args));
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
    /*@ invariant [_]world(ss_pub, ss_key_clsfy) &*& 
          principal(sender, _) &*&
          principal(receiver, _) &*&
          item(s_key, symmetric_key_item(sender, _), ss_pub) &*&
          item(r_key, symmetric_key_item(sender, _), ss_pub);
    @*/
  {
    pthread_t s_thread, r_thread;
    struct ss_args *args_s = malloc(sizeof(struct ss_args));
    if (args_s == 0) abort();
    struct ss_args *args_r = malloc(sizeof(struct ss_args));
    if (args_r == 0) abort();
    args_s->key = s_key;
    args_r->key = r_key;
    {
      /*@ close pthread_run_pre(sender_t)(args_s, cons(pointer_value(s_key),
                          cons(int_value(sender), cons(int_value(receiver), nil)))); @*/
      pthread_create(&s_thread, null, &sender_t, args_s);
      /*@ close pthread_run_pre(receiver_t)(args_r, cons(pointer_value(r_key),                        
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
