#include "asymmetric_encrypted_item.h"

struct item *asymmetric_authenticated_encryption(int recipient,
                                                 struct item *public_key,
                                                 struct item *private_key,
                                                 struct item *payload)
  /*@ requires [?f]world(?pub, ?key_clsfy) &*&
               principal(?principal1, ?count1) &*&
               item(public_key, ?pub_k, pub) &*&
                 pub_k == public_key_item(?principal2, ?count2) &*&
               item(private_key, ?priv_k, pub) &*&
                 priv_k == private_key_item(?principal3, ?count3) &*&
               item(payload, ?pay, pub); @*/
  /*@ ensures  [f]world(pub, key_clsfy) &*&
               principal(principal1, count1 + 2) &*&
               item(public_key, pub_k, pub) &*&
               item(private_key, priv_k, pub) &*&
               item(payload, pay, pub) &*&
               item(result, ?msg, pub) &*&
               col ? true :
                 msg == pair_item(?enc, ?sig) &*&
                 enc == asymmetric_encrypted_item(principal2, count2,
                                                  some(pay), _) &*&
                 sig == asymmetric_signature_item(principal3, count3,
                                                  some(?msg_id), _) &*&
                 msg_id == pair_item(data_item(chars_of_int(recipient)),
                                     hash_item(some(enc))); @*/
{
  struct item* encrypted = asymmetric_encryption(public_key, payload);
  //@ assert item(encrypted, ?e, pub);
  /*@ if (col)
      {
        retreive_proof_obligations();
        open proof_obligations(pub);
        assert is_public_collision(?proof, pub);
        proof(e);
        close proof_obligations(pub);
        leak proof_obligations(pub);
      }
  @*/
  struct item* hash = create_hash(encrypted);
  struct item* rcp = create_data_item_from_int(recipient);
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

struct item *asymmetric_authenticated_decryption(int recipient, char tag,
                                                 struct item *public_key,
                                                 struct item *private_key,
                                                 struct item *message)
  /*@ requires [?f]world(?pub, ?key_clsfy) &*& true == valid_tag(tag) &*&
               principal(?principal1, ?count1) &*&
               item(public_key, ?pub_k, pub) &*&
                 pub_k == public_key_item(?principal2, ?count2) &*&
               item(private_key, ?priv_k, pub) &*&
                 priv_k == private_key_item(?principal3, ?count3) &*&
               item(message, ?msg, pub); @*/
  /*@ ensures  [f]world(pub, key_clsfy) &*&
               principal(principal1, count1 + 1) &*&
               item(public_key, pub_k, pub) &*&
               item(private_key, priv_k, pub) &*&
               item(message, msg, pub) &*&
               item(result, ?decrypted, pub) &*&
               col ? [_]pub(decrypted) :
                 tag_for_item(decrypted) == tag &*&
                 msg == pair_item(?enc, ?sig) &*&
                 enc == asymmetric_encrypted_item(?principal4, ?count4,
                                                  ?pay, _) &*&
                 sig == asymmetric_signature_item(?principal5, ?count5,
                                                  some(?msg_id), _) &*&
                 principal3 != principal4 || count3 != count4 ?
                   
                   true == key_clsfy(principal3, count3, false) &*&
                   [_]pub(decrypted) 
                 :
                   msg_id == pair_item(data_item(chars_of_int(recipient)),
                                       hash_item(some(enc))) &*&
                   principal2 == principal5 && count2 == count5 &*&
                   switch(pay)
                   {
                     case some(pay2):
                       return pay2 == decrypted;
                     case none:
                       return false;
                   }; @*/
{
  check_is_pair(message);
  struct item* encrypted = pair_get_first(message);
  check_is_asymmetric_encrypted(encrypted);
  struct item* signature = pair_get_second(message);
  struct item* rcp = create_data_item_from_int(recipient);
  //@ assert item(encrypted, ?e, pub);
  /*@ if (col)
      {
        retreive_proof_obligations();
        open proof_obligations(pub);
        assert is_public_collision(?proof, pub);
        proof(e);
        close proof_obligations(pub);
        leak proof_obligations(pub);
      }
  @*/
  struct item* hash = create_hash(encrypted);
  struct item* pair = create_pair(rcp, hash);
  check_is_asymmetric_signature(signature);
  asymmetric_signature_verify(public_key, pair, signature);
  struct item *result = asymmetric_decryption(private_key, encrypted, tag);
  item_free(encrypted);
  item_free(rcp);
  item_free(pair);
  item_free(hash);
  item_free(signature);

  return result;
}
