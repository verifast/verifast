#include "../annotated_api/mbedTLS_definitions.h"

#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

//@ import_module public_invariant_mod;
//@ import_module principals_mod;
//@ import_module decryption_mod;

/*@

#define ATTACKER_PRE(PREFIX) \
  predicate_family_instance pthread_run_pre(attacker_t)(void *data, any info) = \
  [_]public_invar(PREFIX##_pub) &*& \
  public_invariant_constraints(PREFIX##_pub, PREFIX##_proof_pred) &*& \
  [_]decryption_key_classifier(PREFIX##_public_key) &*& \
  is_public_key_classifier(_, PREFIX##_pub, \
                              PREFIX##_public_key, \
                              PREFIX##_proof_pred) &*& \
  exists<int>(?bad_one) &*& info == some(bad_one) &*& true == bad(bad_one) &*& \
  principal(bad_one, _);
  
inductive info =
  | int_value(int v)
  | pointer_value(char* p)
  | char_list_value(list<char> p)
  | crypto_char_list_value(list<crypto_char> p)
;

#define IV(v, next)  cons(int_value(v), next)
#define PV(v, next)  cons(pointer_value(v), next)
#define CL(v, next)  cons(char_list_value(v), next)
#define CCL(v, next) cons(crypto_char_list_value(v), next)

#define PROTOCOL_INIT_WITH_KEY_CLASSIFIER(PREFIX, CLASSIFIER) \
{ \
  open_module(); \
  assert module(public_invariant_mod, true); \
  assert module(principals_mod, true); \
  assert module(decryption_mod, true); \
  PUBLIC_INVARIANT_CONSTRAINTS(PREFIX)  \
  DECRYPTION_CONSTRAINTS(PREFIX) \
  public_invariant_init(PREFIX##_pub); \
  decryption_init(CLASSIFIER); \
  principals_init(); \
}

#define PROTOCOL_INIT(PREFIX) \
  PROTOCOL_INIT_WITH_KEY_CLASSIFIER(PREFIX, PREFIX##_public_key)

@*/
