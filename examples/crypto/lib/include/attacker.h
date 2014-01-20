#ifndef ATTACKER_H
#define ATTACKER_H

#include "dolevyao.h"

#include <pthread.h>

/*@
predicate attacker_proof_obligations(fixpoint(item, bool) pub) =
 is_can_send_bad_principal_keys(_, pub) &*&
 is_can_send_data(_, pub) &*&
 is_can_send_public_pair(_, pub) &*&
 is_can_send_decomposed_public_pair(_, pub) &*&
 is_can_send_public_encrypted(_, pub) &*&
 is_can_send_public_decrypted(_, pub) &*&
 is_can_send_public_hmac(_, pub);
                                                                 
typedef lemma void can_send_bad_principal_keys(fixpoint(item, bool) pub)(int p);
  requires  [?f]world(pub) &*& 
            item(?item, key_item(p, ?c, ?k, int_pair(0, 0))) &*& 
            bad(p) == true;
  ensures   [f]world(pub) &*& 
            item(item, key_item(p, c, k, int_pair(0, 0))) &*& 
            pub(key_item(p, c, k, int_pair(0, 0))) == true;

typedef lemma void can_send_data(fixpoint(item, bool) pub)(int data);
  requires  [?f]world(pub);
  ensures   [f]world(pub) &*& 
            pub(data_item(data)) == true;

typedef lemma void can_send_public_pair(fixpoint(item, bool) pub)();
  requires  [?f]world(pub) &*& 
            item(?i1, ?ii1) &*& pub(ii1) == true &*& 
            item(?i2, ?ii2) &*& pub(ii2) == true;
  ensures   [f]world(pub) &*& 
            item(i1, ii1) &*&
            item(i2, ii2) &*&
            pub(pair_item(ii1, ii2)) == true;

typedef lemma void can_send_decomposed_public_pair(fixpoint(item, bool) pub)();
  requires  [?f]world(pub) &*& 
            item(?i, pair_item(?i1, ?i2)) &*& 
            pub(pair_item(i1, i2)) == true;
  ensures   [f]world(pub) &*& 
            item(i, pair_item(i1, i2)) &*& 
            pub(i1) == true &*& pub(i2) == true;

typedef lemma void can_send_public_encrypted(fixpoint(item, bool) pub)();
  requires  [?f]world(pub) &*& 
            item(?k_item, key_item(?p, ?c, ?k, ?i)) &*& 
            pub(key_item(p, c, k, i)) == true &*&
            item(?p_item, ?payload) &*&
            pub(payload) == true &*&
            item(?e_item, encrypted_item(p, c, k, i, payload, ?e));
  ensures   [f]world(pub) &*& 
            item(k_item, key_item(p, c, k, i)) &*&
            item(p_item, payload) &*&
            item(e_item, encrypted_item(p, c, k, i, payload, e)) &*&
            pub(encrypted_item(p, c, k, i, payload, e)) == true;

typedef lemma void can_send_public_decrypted(fixpoint(item, bool) pub)();
  requires  [?f]world(pub) &*& 
            item(?k_item, key_item(?p, ?c, ?k, ?i)) &*& 
            pub(key_item(p, c, k, i)) == true &*&
            item(?e_item, encrypted_item(p, c, inverse_key_kind(k), i, ?payload, ?e)) &*&
            pub(encrypted_item(p, c, inverse_key_kind(k), i, payload, e)) == true &*&
            item(?p_item, payload);
  ensures   [f]world(pub) &*& 
            item(k_item, key_item(p, c, k, i)) &*&
            item(p_item, payload) &*&
            item(e_item, encrypted_item(p, c, inverse_key_kind(k), i, payload, e)) &*&
            pub(payload) == true;

typedef lemma void can_send_public_hmac(fixpoint(item, bool) pub)();
  requires  [?f]world(pub) &*& 
            item(?k_item, key_item(?p, ?c, ?k, ?i)) &*& 
            pub(key_item(p, c, k, i)) == true &*&
            item(?p_item, ?payload) &*&
            pub(payload) == true &*&
            item(?h_item, hmac_item(p, c, k, i, payload));
  ensures   [f]world(pub) &*& 
            item(k_item, key_item(p, c, k, i)) &*&
            item(p_item, payload) &*&
            item(h_item, hmac_item(p, c, k, i, payload)) &*&
            pub(hmac_item(p, c, k, i, payload)) == true;
@*/

void attacker();
  /*@ requires exists<fixpoint(item, bool)>(?pub) &*& [?f]world(pub) &*&
               attacker_proof_obligations(pub) &*&
               initial_principals() &*& !bad(0);
  @*/
  //@ ensures false;

/*@

#define PACK_ATTACKER_PROOF_OBLIGATIONS(PREFIX) \
{ \
  produce_lemma_function_pointer_chunk(PREFIX##_can_send_bad_principal_keys) : \
    can_send_bad_principal_keys(PREFIX##_pub)(PREFIX##_p){ call(); }; \
  produce_lemma_function_pointer_chunk(PREFIX##_can_send_data) : \
    can_send_data(PREFIX##_pub)(data){ call(); }; \
  produce_lemma_function_pointer_chunk(PREFIX##_can_send_public_pair) : \
    can_send_public_pair(PREFIX##_pub)(){ call(); }; \
  produce_lemma_function_pointer_chunk(PREFIX##_can_send_decomposed_public_pair) : \
    can_send_decomposed_public_pair(PREFIX##_pub)(){ call(); }; \
  produce_lemma_function_pointer_chunk(PREFIX##_can_send_public_encrypted) : \
    can_send_public_encrypted(PREFIX##_pub)(){ call(); }; \
  produce_lemma_function_pointer_chunk(PREFIX##_can_send_public_decrypted) : \
    can_send_public_decrypted(PREFIX##_pub)(){ call(); }; \
  produce_lemma_function_pointer_chunk(PREFIX##_can_send_public_hmac) : \
    can_send_public_hmac(PREFIX##_pub)(){ call(); }; \
}

#define ATTACKER_PROOFS_DEFAULT(PREFIX) \
  DEFAULT_CAN_SEND_BAD_PRINCIPAL_KEYS(PREFIX) \
  DEFAULT_CAN_SEND_DATA(PREFIX) \
  DEFAULT_CAN_SEND_PUBLIC_PAIR(PREFIX) \
  DEFAULT_CAN_SEND_DECOMPOSED_PUBLIC_PAIR(PREFIX) \
  DEFAULT_CAN_SEND_PUBLIC_ENCRYPTED(PREFIX) \
  DEFAULT_CAN_SEND_PUBLIC_DECRYPTED(PREFIX) \
  DEFAULT_CAN_SEND_PUBLIC_HMAC(PREFIX)

#define DEFAULT_CAN_SEND_BAD_PRINCIPAL_KEYS(PREFIX) \
lemma void PREFIX##_can_send_bad_principal_keys(int p) \
  requires [?f]world(PREFIX##_pub) &*& \
           item(?item, key_item(p, ?c, ?k, int_pair(0, 0))) &*& \
           bad(p) == true; \
  ensures  [f]world(PREFIX##_pub) &*& \
           item(item, key_item(p, c, k, int_pair(0, 0))) &*& \
           PREFIX##_pub(key_item(p, c, k, int_pair(0, 0))) == true; \
{ \
  assert true; \
}

#define DEFAULT_CAN_SEND_DATA(PREFIX) \
lemma void PREFIX##_can_send_data(int data) \
  requires [?f]world(PREFIX##_pub); \
  ensures  [f]world(PREFIX##_pub) &*& \
           PREFIX##_pub(data_item(data)) == true; \
{ \
  assert true; \
}

#define DEFAULT_CAN_SEND_PUBLIC_PAIR(PREFIX) \
lemma void PREFIX##_can_send_public_pair() \
  requires  [?f]world(PREFIX##_pub) &*& \
            item(?i1, ?ii1) &*& PREFIX##_pub(ii1) == true &*& \
            item(?i2, ?ii2) &*& PREFIX##_pub(ii2) == true; \
  ensures   [f]world(PREFIX##_pub) &*& \
            item(i1, ii1) &*& \
            item(i2, ii2) &*& \
            PREFIX##_pub(pair_item(ii1, ii2)) == true; \
{ \
  assert true; \
}

#define DEFAULT_CAN_SEND_DECOMPOSED_PUBLIC_PAIR(PREFIX) \
lemma void PREFIX##_can_send_decomposed_public_pair() \
   requires  [?f]world(PREFIX##_pub) &*& \
            item(?i, pair_item(?i1, ?i2)) &*& \
            PREFIX##_pub(pair_item(i1, i2)) == true; \
  ensures   [f]world(PREFIX##_pub) &*& \
            item(i, pair_item(i1, i2)) &*& \
            PREFIX##_pub(i1) == true &*& PREFIX##_pub(i2) == true; \
{ \
  assert true; \
}

#define DEFAULT_CAN_SEND_PUBLIC_ENCRYPTED(PREFIX) \
lemma void PREFIX##_can_send_public_encrypted() \
  requires  [?f]world(PREFIX##_pub) &*& \
            item(?k_item, key_item(?p, ?c, ?k, ?i)) &*& \
            PREFIX##_pub(key_item(p, c, k, i)) == true &*& \
            item(?p_item, ?payload) &*& \
            PREFIX##_pub(payload) == true &*& \
            item(?e_item, encrypted_item(p, c, k, i, payload, ?e)); \
  ensures   [f]world(PREFIX##_pub) &*& \
            item(k_item, key_item(p, c, k, i)) &*& \
            item(p_item, payload) &*& \
            item(e_item, encrypted_item(p, c, k, i, payload, e)) &*& \
            PREFIX##_pub(encrypted_item(p, c, k, i, payload, e)) == true; \
{ \
  assert true; \
}

#define DEFAULT_CAN_SEND_PUBLIC_DECRYPTED(PREFIX) \
  DEPTH_CAN_SEND_PUBLIC_DECRYPTED(PREFIX, 1)

#define DEPTH_CAN_SEND_PUBLIC_DECRYPTED(PREFIX, DEPTH) \
lemma void PREFIX##_can_send_public_decrypted() \
  requires  [?f]world(PREFIX##_pub) &*& \
            item(?k_item, key_item(?p, ?c, ?k, ?i)) &*& \
            PREFIX##_pub(key_item(p, c, k, i)) == true &*& \
            bad(0) == false &*& \
            item(?e_item, encrypted_item(p, c, inverse_key_kind(k), i, ?payload, ?e)) &*& \
            PREFIX##_pub(encrypted_item(p, c, inverse_key_kind(k), i, payload, e)) == true &*& \
            item(?p_item, payload); \
  ensures   [f]world(PREFIX##_pub) &*& \
            item(k_item, key_item(p, c, k, i)) &*& \
            item(p_item, payload) &*& \
            item(e_item, encrypted_item(p, c, inverse_key_kind(k), i, payload, e)) &*& \
            PREFIX##_pub(payload) == true; \
{ \
  SWITCH_CRYPTO_PRIMITIVES(p_item, 1, DEPTH); \
}

#define DEFAULT_CAN_SEND_PUBLIC_HMAC(PREFIX) \
lemma void PREFIX##_can_send_public_hmac() \
  requires  [?f]world(PREFIX##_pub) &*& \
            item(?k_item, key_item(?p, ?c, ?k, ?i)) &*& \
            PREFIX##_pub(key_item(p, c, k, i)) == true &*& \
            item(?p_item, ?payload) &*& \
            PREFIX##_pub(payload) == true &*& \
            item(?h_item, hmac_item(p, c, k, i, payload)); \
  ensures   [f]world(PREFIX##_pub) &*& \
            item(k_item, key_item(p, c, k, i)) &*& \
            item(p_item, payload) &*& \
            item(h_item, hmac_item(p, c, k, i, payload)) &*& \
            PREFIX##_pub(hmac_item(p, c, k, i, payload)) == true; \
{ \
  assert true; \
}

@*/

#endif

