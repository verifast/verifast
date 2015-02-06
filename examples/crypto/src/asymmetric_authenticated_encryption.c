#include "asymmetric_encrypted_item.h"

struct item *asymmetric_authenticated_encryption(char recipient,
                                                 struct item *public_key,
                                                 struct item *private_key, 
                                                 struct item *payload)
  /*@ requires [?f]world(?pub) &*&
               generated_values(?principal1, ?count1) &*&
               item(public_key, ?pub_k, pub) &*& 
                 pub_k == public_key_item(?principal2, ?count2) &*&
               item(private_key, ?priv_k, pub) &*& 
                 priv_k == private_key_item(?principal3, ?count3) &*&
               item(payload, ?pay, pub); @*/
  /*@ ensures  [f]world(pub) &*&
               generated_values(principal1, count1 + 2) &*&
               item(public_key, pub_k, pub) &*&
               item(private_key, priv_k, pub) &*&
               item(payload, pay, pub) &*&
               item(result, ?msg, pub) &*& 
               collision_in_run() ?
                 true
               :
                 msg == pair_item(?enc, ?sig) &*&
                 enc == asymmetric_encrypted_item(principal2, count2, 
                                                  some(pay), _) &*&
                 sig == asymmetric_signature_item(principal3, count3, 
                                                  some(?msg_id), _) &*&
                 msg_id == pair_item(data_item(cons(recipient, nil)), 
                                     hash_item(some(enc))); @*/
{
  struct item* encrypted = asymmetric_encryption(public_key, payload);
  struct item* hash = create_hash(encrypted);
  struct item* rcp = create_data_item_from_char(recipient);
  struct item* msg_id = create_pair(rcp, hash);
  struct item* signature = asymmetric_signature(private_key, msg_id);
  struct item* result = create_pair(encrypted, signature);
  item_free(encrypted);
  item_free(hash);
  item_free(rcp);
  item_free(msg_id);
  item_free(signature);
  return result;
}

struct item *asymmetric_authenticated_decryption(char recipient,
                                                 struct item *public_key,
                                                 struct item *private_key, 
                                                 struct item *message)
  /*@ requires [?f]world(?pub) &*&
               generated_values(?principal1, ?count1) &*&
               item(public_key, ?pub_k, pub) &*& 
                 pub_k == public_key_item(?principal2, ?count2) &*&
               item(private_key, ?priv_k, pub) &*& 
                 priv_k == private_key_item(?principal3, ?count3) &*&
               item(message, ?msg, pub); @*/
  /*@ ensures  [f]world(pub) &*&
               generated_values(principal1, count1 + 1) &*&
               item(public_key, pub_k, pub) &*&
               item(private_key, priv_k, pub) &*&
               item(message, msg, pub) &*&
               item(result, ?decrypted, pub) &*& 
               collision_in_run() ?
                 true
               :
                 msg == pair_item(?enc, ?sig) &*& 
                 enc == asymmetric_encrypted_item(?principal4, ?count4, 
                                                  ?pay, _) &*&
                 sig == asymmetric_signature_item(principal2, count2, 
                                                  some(?msg_id), _) &*&
                 msg_id == pair_item(data_item(cons(recipient, nil)), 
                                     hash_item(some(enc))) &*&
                 principal4 == principal3 && count4 == count3 ?
                   pay == some(decrypted)
                 :
                   [_]pub(decrypted)
               ; @*/
{
  check_is_pair(message);
  struct item* encrypted = pair_get_first(message);
  check_is_asymmetric_encrypted(encrypted);
  struct item* signature = pair_get_second(message);
  struct item* rcp = create_data_item_from_char(recipient);  
  struct item* hash = create_hash(encrypted);
  struct item* pair = create_pair(rcp, hash);
  asymmetric_signature_verify(public_key, pair, signature);
  struct item *result = asymmetric_decryption(private_key, encrypted);
  item_free(encrypted);
  item_free(rcp);
  item_free(pair);
  item_free(hash);
  item_free(signature);
  
  return result;
}
