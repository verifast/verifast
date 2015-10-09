#include "yahalom.h"

#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

//@ import_module public_invariant_mod;
//@ import_module principals_mod;

/*@
predicate_family_instance pthread_run_pre(attacker_t)(void *data, any info) =
    [_]public_invar(yahalom_pub) &*&
    public_invariant_constraints(yahalom_pub, yahalom_proof_pred) &*&
    principals(_) &*& principal(?attacker, _) &*& true == bad(attacker);
@*/

void *attacker_t(void* data) //@ : pthread_run_joinable
  //@ requires pthread_run_pre(attacker_t)(data, ?info);
  //@ ensures  false;
{
  while(true)
    //@ invariant pthread_run_pre(attacker_t)(data, info);
  {
    //@ open pthread_run_pre(attacker_t)(data, info);
    //@ assert principal(?attacker, _);
    //@ close exists(attacker);
    //@ close yahalom_proof_pred();
    attacker();
    //@ open yahalom_proof_pred();
    //@ close pthread_run_pre(attacker_t)(data, info);
  }
   
  return 0;
}

struct yahalom_args
{
  int server;
  int sender;
  int receiver;
  
  char* s_key;
  char* r_key;
  char* key;
};

/*@
inductive info =
  | int_value(int v)
  | pointer_value(char* p)
  | char_list_value(list<char> p)
;

predicate_family_instance pthread_run_pre(server_t)(void *data, any info) =
  [_]public_invar(yahalom_pub) &*&
  yahalom_args_server(data, ?server) &*&
  yahalom_args_sender(data, ?sender) &*&
  yahalom_args_receiver(data, ?receiver) &*&
  yahalom_args_s_key(data, ?s_key) &*&
  yahalom_args_r_key(data, ?r_key) &*&
  principal(server, _) &*&
  [1/2]cryptogram(s_key, KEY_SIZE, ?s_key_cs, ?s_key_cg) &*&
    s_key_cg == cg_symmetric_key(sender, ?s_id) &*&
    cg_info(s_key_cg) == int_pair(3, server) &*&
  [1/2]cryptogram(r_key, KEY_SIZE, ?r_key_cs, ?r_key_cg) &*&
    r_key_cg == cg_symmetric_key(receiver, ?r_id) &*&
    cg_info(r_key_cg) == int_pair(3, server) &*&
  info == cons(int_value(server), 
            cons(int_value(sender), 
              cons(int_value(receiver), 
                cons(pointer_value(s_key),
                  cons(char_list_value(s_key_cs),
                    cons(int_value(s_id),
                      cons(pointer_value(r_key),
                        cons(char_list_value(r_key_cs),
                          cons(int_value(r_id),
                               nil)))))))));

predicate_family_instance pthread_run_post(server_t)(void *data, any info) =
  [_]public_invar(yahalom_pub) &*&
  yahalom_args_server(data, ?server) &*&
  yahalom_args_sender(data, ?sender) &*&
  yahalom_args_receiver(data, ?receiver) &*&
  yahalom_args_s_key(data, ?s_key) &*&
  yahalom_args_r_key(data, ?r_key) &*&
  principal(server, _) &*&
  [1/2]cryptogram(s_key, KEY_SIZE, ?s_key_cs, ?s_key_cg) &*&
    s_key_cg == cg_symmetric_key(sender, ?s_id) &*&
  [1/2]cryptogram(r_key, KEY_SIZE, ?r_key_cs, ?r_key_cg) &*&
    r_key_cg == cg_symmetric_key(receiver, ?r_id) &*&
  info == cons(int_value(server), 
            cons(int_value(sender), 
              cons(int_value(receiver), 
                cons(pointer_value(s_key),
                  cons(char_list_value(s_key_cs),
                    cons(int_value(s_id),
                      cons(pointer_value(r_key),
                        cons(char_list_value(r_key_cs),
                          cons(int_value(r_id),
                               nil)))))))));
@*/

void *server_t(void* data) //@ : pthread_run_joinable
  //@ requires pthread_run_pre(server_t)(data, ?x);
  //@ ensures pthread_run_post(server_t)(data, x) &*& result == 0;
{
  struct yahalom_args *args = data;
  //@ open pthread_run_pre(server_t)(data, _);
  server(args->server, args->sender, args->receiver, 
         args->s_key, args->r_key);
  //@ close pthread_run_post(server_t)(data, _);
  return 0;
}

/*@
predicate_family_instance pthread_run_pre(sender_t)(void *data, any info) =
  [_]public_invar(yahalom_pub) &*&
  yahalom_args_server(data, ?server) &*&
  yahalom_args_sender(data, ?sender) &*&
  yahalom_args_receiver(data, ?receiver) &*&
  yahalom_args_s_key(data, ?s_key) &*&
  yahalom_args_key(data, ?key) &*&
  principal(sender, _) &*&
  [1/2]cryptogram(s_key, KEY_SIZE, ?s_key_cs, ?s_key_cg) &*&
    s_key_cg == cg_symmetric_key(sender, ?s_id) &*&
    cg_info(s_key_cg) == int_pair(3, server) &*&
  chars(key, KEY_SIZE, _) &*&
  info == cons(int_value(server), 
            cons(int_value(sender), 
              cons(int_value(receiver), 
                cons(pointer_value(s_key),
                  cons(char_list_value(s_key_cs),
                    cons(int_value(s_id),
                      cons(pointer_value(key),
                           nil)))))));

predicate_family_instance pthread_run_post(sender_t)(void *data, any info) =
  [_]public_invar(yahalom_pub) &*&
  yahalom_args_server(data, ?server) &*&
  yahalom_args_sender(data, ?sender) &*&
  yahalom_args_receiver(data, ?receiver) &*&
  yahalom_args_s_key(data, ?s_key) &*&
  yahalom_args_key(data, ?key) &*&
  principal(sender, _) &*&
  [1/2]cryptogram(s_key, KEY_SIZE, ?s_key_cs, ?s_key_cg) &*&
    s_key_cg == cg_symmetric_key(sender, ?s_id) &*&
  cryptogram(key, KEY_SIZE, _, ?key_cg) &*&
    collision_in_run || bad(server) || bad(sender) ||
    int_left(cg_info(key_cg)) == 4 &*&
  info == cons(int_value(server), 
            cons(int_value(sender), 
              cons(int_value(receiver), 
                cons(pointer_value(s_key),
                  cons(char_list_value(s_key_cs),
                    cons(int_value(s_id),
                      cons(pointer_value(key),
                           nil)))))));
@*/

void *sender_t(void* data) //@ : pthread_run_joinable
  //@ requires pthread_run_pre(sender_t)(data, ?x);
  //@ ensures pthread_run_post(sender_t)(data, x) &*& result == 0;
{
  struct yahalom_args *args = data;
  //@ open pthread_run_pre(sender_t)(data, _);
  sender(args->server, args->sender, args->receiver, 
         args->s_key, args->key);
  //@ close pthread_run_post(sender_t)(data, _);
  return 0;
}

/*@
predicate_family_instance pthread_run_pre(receiver_t)(void *data, any info) =
  [_]public_invar(yahalom_pub) &*&
  yahalom_args_server(data, ?server) &*&
  yahalom_args_sender(data, ?sender) &*&
  yahalom_args_receiver(data, ?receiver) &*&
  yahalom_args_r_key(data, ?r_key) &*&
  yahalom_args_key(data, ?key) &*&
  principal(receiver, _) &*&
  [1/2]cryptogram(r_key, KEY_SIZE, ?r_key_cs, ?r_key_cg) &*&
    r_key_cg == cg_symmetric_key(receiver, ?r_id) &*&
    cg_info(r_key_cg) == int_pair(3, server) &*&
  chars(key, KEY_SIZE, _) &*&
  info == cons(int_value(server), 
            cons(int_value(sender), 
              cons(int_value(receiver), 
                cons(pointer_value(r_key),
                  cons(char_list_value(r_key_cs),
                    cons(int_value(r_id),
                      cons(pointer_value(key),
                           nil)))))));

predicate_family_instance pthread_run_post(receiver_t)(void *data, any info) =
  [_]public_invar(yahalom_pub) &*&
  yahalom_args_server(data, ?server) &*&
  yahalom_args_sender(data, ?sender) &*&
  yahalom_args_receiver(data, ?receiver) &*&
  yahalom_args_r_key(data, ?r_key) &*&
  yahalom_args_key(data, ?key) &*&
  principal(receiver, _) &*&
  [1/2]cryptogram(r_key, KEY_SIZE, ?r_key_cs, ?r_key_cg) &*&
    r_key_cg == cg_symmetric_key(receiver, ?r_id) &*&
  cryptogram(key, KEY_SIZE, _, ?key_cg) &*&
    collision_in_run || bad(server) || bad(sender) || bad(receiver) ||
    int_left(cg_info(key_cg)) == 4 &*&
  info == cons(int_value(server), 
            cons(int_value(sender), 
              cons(int_value(receiver), 
                cons(pointer_value(r_key),
                  cons(char_list_value(r_key_cs),
                    cons(int_value(r_id),
                      cons(pointer_value(key),
                           nil)))))));
@*/

void *receiver_t(void* data) //@ : pthread_run_joinable
  //@ requires pthread_run_pre(receiver_t)(data, ?x);
  //@ ensures pthread_run_post(receiver_t)(data, x) &*& result == 0;
{
  struct yahalom_args *args = data;
  //@ open pthread_run_pre(receiver_t)(data, _);
  receiver(args->server, args->sender, args->receiver, 
           args->r_key, args->key);
  //@ close pthread_run_post(receiver_t)(data, _);
  return 0;
}

int main(int argc, char **argv) //@ : main_full(main_app)
    //@ requires module(main_app, true);
    //@ ensures true;
{
  //@ open_module();

  pthread_t a_thread;
  havege_state havege_state;
  
  printf("\n\tExecuting \"");
  printf("yahalom protocol");
  printf("\" ... \n\n");
  
  //@ PUBLIC_INVARIANT_CONSTRAINTS(yahalom)
  //@ public_invariant_init(yahalom_pub);
  
  //@ principals_init();
  //@ int server = principal_create();
  //@ assert server == 1;
  //@ int sender = principal_create();
  //@ assert sender == 2;
  //@ int receiver = principal_create();
  //@ assert receiver == 3;
  
  //@ int attacker = principal_create();
  //@ assume (bad(attacker));
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
    /*@ invariant [_]public_invar(yahalom_pub) &*&
                  havege_state_initialized(&havege_state) &*&
                  principal(server, ?serv_count) &*&
                  principal(sender, ?send_count) &*&
                  principal(receiver, ?rcvr_count);
    @*/
  {
    char s_key[KEY_SIZE];
    char r_key[KEY_SIZE];
    char key1[KEY_SIZE];
    char key2[KEY_SIZE];
    
    //@ close random_request(sender, int_pair(3, server), true);
    if (havege_random(&havege_state, s_key, KEY_SIZE) != 0) abort();
    //@ assert cryptogram(s_key, KEY_SIZE, ?cs_s_key, ?cg_s_key);
    //@ assert cg_s_key == cg_symmetric_key(sender, send_count + 1);
    //@ close random_request(receiver, int_pair(3, server), true);
    if (havege_random(&havege_state, r_key, KEY_SIZE) != 0) abort();
    //@ assert cryptogram(r_key, KEY_SIZE, ?cs_r_key, ?cg_r_key);
    //@ assert cg_r_key == cg_symmetric_key(receiver, rcvr_count + 1);
    
    {
      pthread_t serv_thread, s_thread, r_thread;
      struct yahalom_args serv_args, s_args, r_args;
      
      serv_args.server = 1;
      serv_args.sender = 2;
      serv_args.receiver = 3;
      serv_args.s_key = s_key;
      serv_args.r_key = r_key;
      
      s_args.server = 1;
      s_args.sender = 2;
      s_args.receiver = 3;
      s_args.s_key = s_key;
      s_args.key = key1;
      
      r_args.server = 1;
      r_args.sender = 2;
      r_args.receiver = 3;
      r_args.r_key = r_key;
      r_args.key = key2;
      
      //@ close pthread_run_pre(server_t)(&serv_args, ?serv_data);
      pthread_create(&serv_thread, NULL, &server_t, &serv_args);
      //@ close pthread_run_pre(sender_t)(&s_args, ?s_data);
      pthread_create(&s_thread, NULL, &sender_t, &s_args);
      //@ close pthread_run_pre(receiver_t)(&r_args, ?r_data);
      pthread_create(&r_thread, NULL, &receiver_t, &r_args);
      
      pthread_join(serv_thread, NULL);
      //@ open pthread_run_post(server_t)(&serv_args, serv_data);
      pthread_join(s_thread, NULL);
      //@ open pthread_run_post(sender_t)(&s_args, s_data);
      pthread_join(r_thread, NULL);
      //@ open pthread_run_post(receiver_t)(&r_args, r_data);
    }

    //@ open cryptogram(key1, KEY_SIZE, ?cs_key1, _);
    //@ close optional_crypto_chars(!collision_in_run, key1, KEY_SIZE, cs_key1);
    zeroize(key1, KEY_SIZE);
    //@ open cryptogram(key2, KEY_SIZE, ?cs_key2, _);
    //@ close optional_crypto_chars(!collision_in_run, key2, KEY_SIZE, cs_key2);
    zeroize(key2, KEY_SIZE);
    //@ close optional_crypto_chars(!collision_in_run, s_key, KEY_SIZE, cs_s_key);
    zeroize(s_key, KEY_SIZE);
    //@ close optional_crypto_chars(!collision_in_run, r_key, KEY_SIZE, cs_r_key);
    zeroize(r_key, KEY_SIZE);
  }
  
  printf("\n\n\t\tDone\n");
  return 0;
}

