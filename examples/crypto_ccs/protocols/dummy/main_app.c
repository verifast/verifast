#include "dummy.h"

#include "../general.h"

//@ ATTACKER_PRE(dummy)

void *attacker_t(void* data) //@ : pthread_run_joinable
  //@ requires pthread_run_pre(attacker_t)(data, ?info);
  //@ ensures  false;
{
  while(true)
    //@ invariant pthread_run_pre(attacker_t)(data, info);
  {
    //@ open pthread_run_pre(attacker_t)(data, info);
    //@ close dummy_proof_pred();
    attacker();
    //@ open dummy_proof_pred();
    //@ close pthread_run_pre(attacker_t)(data, info);
  }
}

/*@

predicate_family_instance pthread_run_pre(sender_t)(void *data, any info) =
  principal(?sender, _) &*&
  chars(data, PACKAGE_SIZE, ?cs) &*&
  info == IV(sender, CL(cs, nil))
;

predicate_family_instance pthread_run_post(sender_t)(void *data, any info) =
  principal(?sender, _) &*&
  chars(data, PACKAGE_SIZE, ?cs) &*&
  info == IV(sender, CL(cs, nil))
;

@*/

void *sender_t(void *data) //@ : pthread_run_joinable
  //@ requires pthread_run_pre(sender_t)(data, ?x);
  //@ ensures pthread_run_post(sender_t)(data, x) &*& result == 0;
{
  //@ open pthread_run_pre(sender_t)(data, _);
  sender(data);
  //@ close pthread_run_post(sender_t)(data, x);
  return 0;
}

/*@
predicate_family_instance pthread_run_pre(receiver_t)(void *data, any info) = 
  principal(?receiver, _) &*&
  chars_(data, PACKAGE_SIZE, _) &*&
  info == cons(int_value(receiver), nil)
;

predicate_family_instance pthread_run_post(receiver_t)(void *data, any info) = 
  principal(?receiver, _) &*&
  chars(data, PACKAGE_SIZE, _) &*&
  info == cons(int_value(receiver), nil)
;
@*/

void *receiver_t(void* data) //@ : pthread_run_joinable
  //@ requires pthread_run_pre(receiver_t)(data, ?x);
  //@ ensures pthread_run_post(receiver_t)(data, x) &*& result == 0;
{
  //@ open pthread_run_pre(receiver_t)(data, _);
  receiver(data);
  //@ close pthread_run_post(receiver_t)(data, x);
  return 0;
}

int main(int argc, char **argv) //@ : main_full(main_app)
    //@ requires module(main_app, true);
    //@ ensures true;
{
  pthread_t a_thread;
  havege_state havege_state;
  
  printf("\n\tExecuting \"");
  printf("dummy protocol");
  printf("\" ... \n\n");
  
  //@ PROTOCOL_INIT(dummy)
  //@ int attacker = principal_create();
  //@ int sender = principal_create();
  //@ int receiver = principal_create();
  
  //@ assume (bad(attacker));
  //@ close exists(attacker);
  //@ close pthread_run_pre(attacker_t)(NULL, some(attacker));
  pthread_create(&a_thread, NULL, &attacker_t, NULL);
  
  //@ close havege_state(&havege_state);
  havege_init(&havege_state);
  int i = 0;
#ifdef EXECUTE
  while (i++ < 10)
#else
  while (true)
#endif
    /*@ invariant [_]public_invar(dummy_pub) &*&
                  havege_state_initialized(&havege_state) &*&
                  principal(sender, _) &*& principal(receiver, _);
    @*/
  {
    char msg1[PACKAGE_SIZE];
    //@ close random_request(sender, 0, false);
    //@ open principal(sender, _);
    if (havege_random(&havege_state, msg1, PACKAGE_SIZE) != 0) abort();
    //@ close principal(sender, _);
    //@ assert cryptogram(msg1, PACKAGE_SIZE, ?cs, ?cg);
    //@ close dummy_pub(cg);
    //@ leak dummy_pub(cg);
    //@ public_cryptogram(msg1, cg);
    char msg2[PACKAGE_SIZE];
    {
      pthread_t s_thread, c_thread;
      
      //@ close pthread_run_pre(sender_t)(msg1, _);
      pthread_create(&s_thread, NULL, &sender_t, msg1);
      //@ close pthread_run_pre(receiver_t)(msg2, _);
      pthread_create(&c_thread, NULL, &receiver_t, msg2);
      
      pthread_join(s_thread, NULL);
      //@ open pthread_run_post(sender_t)(msg1, _);
      pthread_join(c_thread, NULL);
      //@ open pthread_run_post(receiver_t)(msg2, _);
      
      //@ chars_to_crypto_chars(msg1, PACKAGE_SIZE);
      //@ chars_to_crypto_chars(msg2, PACKAGE_SIZE);
      //@ open principal(sender, _);
      //@ MEMCMP_PUB(msg1)
      //@ MEMCMP_PUB(msg2)
      if (crypto_memcmp(msg1, msg2, PACKAGE_SIZE) != 0)
        abort();
      //@ close principal(sender, _);
      printf(" |%i| ", i);
      //@ crypto_chars_to_chars(msg1, PACKAGE_SIZE);
      //@ crypto_chars_to_chars(msg2, PACKAGE_SIZE);
    }
  }
#ifdef EXECUTE
  printf("\n\n\t\tDone\n");
  return 0;
#endif
}

