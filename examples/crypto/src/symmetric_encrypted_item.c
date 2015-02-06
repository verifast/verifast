#include "symmetric_encrypted_item.h"

#include "item_constraints.h"
#include "key_item.h"
#include "principals.h"
#include "serialization.h"
#include "deserialization.h"

#include <string.h>

bool is_symmetric_encrypted(struct item *item)
  //@ requires item(item, ?i, ?pub);
  /*@ ensures  item(item, i, pub) &*&
               result ? i == symmetric_encrypted_item(_, _, _, _) : true; @*/
{
  //@ open item(item, i, pub);
  //@ assert item->content |-> ?cont;
  //@ open chars(cont, ?size, ?cs);
  //@ open item_constraints(?b, i, cs, pub);
  //@ if (!b) open [_]item_constraints_no_collision(i, cs, pub);
  return *(item->content) == 'i';
  //@ close chars(cont, size, cs);
  //@ close item(item, i, pub);
}

void check_is_symmetric_encrypted(struct item *item)
  //@ requires item(item, ?i, ?pub);
  //@ ensures  item(item, i, pub) &*& i == symmetric_encrypted_item(_, _, _, _);
{
  if (!is_symmetric_encrypted(item))
    abort_crypto_lib("Presented item is not an encrypted item");
}

/*@
lemma void info_for_symmetric_encrypted_item(item key, item enc)
  requires [_]info_for_item(key, ?info1) &*&
           key == symmetric_key_item(?p, ?c) &*&
           [_]info_for_item(enc, ?info2) &*&
           enc == symmetric_encrypted_item(p, c, _, _);
  ensures  info1 == info2;
{
  open [_]info_for_item(key, info1);
  open [_]info_for_item(enc, info2);
}
@*/

struct item *symmetric_encryption(struct item *key, struct item *payload)
  /*@ requires [?f]world(?pub) &*&
               generated_values(?principal1, ?count1) &*&
               item(payload, ?pay, pub) &*& item(key, ?k, pub) &*& 
               k == symmetric_key_item(?principal2, ?count2); @*/
  /*@ ensures  [f]world(pub) &*&
               generated_values(principal1, count1 + 1) &*&
               item(payload, pay, pub) &*& item(key, k, pub) &*& 
               item(result, ?enc, pub) &*& 
               collision_in_run() ?
                 true
               :
                 enc == symmetric_encrypted_item(principal2, count2, 
                                                 some(pay), ?ent); @*/
{
  debug_print("ENCRYPTING:\n");
  print_item(payload);

  struct item* result;
  result = malloc(sizeof(struct item));
  if (result == 0) abort_crypto_lib("Malloc failed");
  
  {
    gcm_context gcm_context;
    char iv_buffer[GCM_IV_SIZE];
    char *iv;
    char *result_cs;
    char *tag;
    char *encrypted;

    //@ close gcm_context(&gcm_context);
    //@ open item(key, k, pub);
    //@ assert key->content |-> ?key_cont &*& key->size |-> ?key_size;
    //@ assert chars(key_cont, key_size, ?key_cs);
    //@ open [_]item_constraints(?b, k, key_cs, pub);
    //@ if (!b) open [_]item_constraints_no_collision(k, key_cs, pub);
    check_valid_symmetric_key_item_size(key->size);
    //@ assert key_size == GCM_KEY_SIZE + 1;
    //@ chars_limits(key_cont);
    //@ chars_split(key_cont, 1);
    //@ assert chars(key_cont + 1, GCM_KEY_SIZE, ?key_cs0);
    //@ polarssl_cryptogram key_cg = polarssl_symmetric_key(principal2, count2);
    //@ close exists(key_cg);
    if (gcm_init(&gcm_context, POLARSSL_AES_CIPHER_ID, (key->content + 1), 
                (unsigned int) GCM_KEY_SIZE * 8) != 0) 
      abort_crypto_lib("Init gcm failed");
    //@ assert gcm_context_initialized(&gcm_context, ?key_id);
    //@ close item(key, k, pub);

    //@ open item(payload, pay, pub);
    //@ assert payload->content |-> ?pay_cont &*& payload->size |-> ?pay_size;
    //@ assert chars(pay_cont, pay_size, ?pay_cs);
    //@ chars_limits(pay_cont);
    if (payload->size >= INT_MAX - (int) sizeof(char) - GCM_ENT_SIZE ||
        payload->size < POLARSSL_MIN_ENCRYPTED_BYTE_SIZE) 
      abort_crypto_lib("Gcm encryption failed: incorrect sizes");
      
    result->size = (int) sizeof(char) + GCM_ENT_SIZE + payload->size;
    result->content = malloc(result->size);
    //@ assert result->content |-> ?r_cont;
    if (result->content == 0)
      abort_crypto_lib("Malloc failed");
    //@ chars_split(r_cont, 1);
    *(result->content) = 'i';
    //@ assert chars(r_cont, 1, cons('i', nil));
    //@ assert chars(r_cont + 1, GCM_ENT_SIZE + pay_size,_);
    tag = result->content + 1;
    //@ open chars(tag, 0, _);
    //@ chars_split(tag, GCM_TAG_SIZE);
    //@ assert chars(tag, GCM_TAG_SIZE, _);
    //@ assert chars(tag + GCM_TAG_SIZE, GCM_IV_SIZE + pay_size,_);
    //@ chars_limits(tag);
    iv = tag + GCM_TAG_SIZE;
    //@ chars_split(iv, GCM_IV_SIZE);
    random_buffer(iv, GCM_IV_SIZE);
    memcpy(iv_buffer, iv, GCM_IV_SIZE);
    //@ assert chars(iv, GCM_IV_SIZE, ?iv_cs);
    encrypted = iv + GCM_IV_SIZE;
    //@ assert chars(encrypted, pay_size, _);
    
    if (gcm_crypt_and_tag(&gcm_context, POLARSSL_GCM_ENCRYPT, 
                          (unsigned int) payload->size,
                          iv_buffer, GCM_IV_SIZE, NULL, 0,
                          payload->content, encrypted,
                          GCM_TAG_SIZE, tag) != 0)
      abort_crypto_lib("Gcm encryption failed");
    
    //@ polarssl_cryptogram k_cg = polarssl_symmetric_key(principal2, count2);
    /*@ if (collision_in_run())
        {
          if (key_cs0 == polarssl_chars_for_cryptogram(k_cg))
            open polarssl_cryptogram(encrypted, pay_size, _, _);
          
          item r = dummy_item_for_tag('i');
          assert chars(iv, GCM_IV_SIZE, iv_cs);
          assert chars(encrypted, pay_size, _);
          
          chars_join(iv);
          chars_join(tag);          
          assert chars(r_cont, 1 + GCM_TAG_SIZE + GCM_IV_SIZE + pay_size, ?cs);
          collision_public(pub, cs);
          close item_constraints(true, r, cs, pub);
          leak item_constraints(true, r, cs, pub);
          close item(result, r, pub);
        }
        else
        {
          assert key_cs0 == polarssl_chars_for_cryptogram(k_cg);
          
          assert chars(tag, GCM_TAG_SIZE, ?tag_cs);
          open polarssl_cryptogram(encrypted, pay_size, ?enc_cs, ?enc_cg);
          assert enc_cg == polarssl_auth_encrypted(
                                     principal2, count2, tag_cs, pay_cs, iv_cs);
          list<char> ent1 = append(tag_cs, iv_cs);
          list<char> ent2 = cons(length(tag_cs), ent1);
          list<char> ent = append(ent1, ent2);
          take_append(GCM_ENT_SIZE, ent1, ent2);
          drop_append(GCM_ENT_SIZE, ent1, ent2);
          item r = symmetric_encrypted_item(principal2, count2, some(pay), ent);
          chars_join(iv);
          chars_join(tag);
          assert chars(r_cont, 1 + GCM_TAG_SIZE + GCM_IV_SIZE + pay_size, ?cs);
          assert cs == cons('i', append(tag_cs, append (iv_cs, enc_cs)));
          append_assoc(tag_cs, iv_cs, enc_cs);
          take_append(GCM_ENT_SIZE, ent1, enc_cs);
          drop_append(GCM_ENT_SIZE, ent1, enc_cs);
          take_append(GCM_TAG_SIZE, tag_cs, iv_cs);
          drop_append(GCM_TAG_SIZE, tag_cs, iv_cs);
          assert enc_cs == polarssl_chars_for_cryptogram(enc_cg);
          item_constraints_well_formed(pay, r);
          close symmetric_encryption_entropy(r)(tag_cs, iv_cs);
          leak symmetric_encryption_entropy(r)(tag_cs, iv_cs);
          open [_]item_constraints(_, pay, pay_cs, pub);
          close item_constraints_no_collision(r, cs, pub);
          leak item_constraints_no_collision(r, cs, pub);
          close item_constraints(false, r, cs, pub);
          leak item_constraints(false, r, cs, pub);
          close item(result, r, pub);
        }
    @*/
    //@ close item(payload, pay, pub);
    gcm_free(&gcm_context);
    //@ open gcm_context(&gcm_context);
  }

  debug_print("ENCRYPTING RESULT:\n");
  print_item(result);

  return result;
}

void check_valid_symmetric_encrypted_item_size(int size)
  //@ requires true;
  //@ ensures  size > 1 + GCM_ENT_SIZE;
{
  if (size <= 1 + GCM_KEY_SIZE)
    abort_crypto_lib("Illegal size for symmetric encrypted item");
}

struct item *symmetric_decryption(struct item *key, struct item *item)
  /*@ requires [?f]world(?pub) &*&
               item(item, ?enc, pub) &*& item(key, ?k, pub) &*&
               enc == 
                  symmetric_encrypted_item(?principal1, ?count1, ?pay, ?ent) &*&
               k == symmetric_key_item(?principal2, ?count2); @*/
  /*@ ensures  [f]world(pub) &*&
               item(item, enc, pub) &*& item(key, k, pub) &*&
               item(result, ?dec, pub) &*& 
               collision_in_run() ?
                 true
               :
                 count1 == count2 && principal1 == principal2 &&
                 pay == some(dec); @*/
{
  debug_print("DECRYPTING:\n");
  print_item(item);

  struct item* result;
  result = malloc(sizeof(struct item));
  if (result == 0) abort_crypto_lib("Malloc failed");
  
  {
    gcm_context gcm_context;
    char *tag;
    char tag_buffer[GCM_IV_SIZE];
    char *iv;
    char iv_buffer[GCM_IV_SIZE];
    char *encrypted;

    //@ close gcm_context(&gcm_context);
    //@ open item(key, k, pub);
    //@ assert key->content |-> ?key_cont &*& key->size |-> ?key_size;
    //@ assert chars(key_cont, key_size, ?key_cs);
    //@ open [_]item_constraints(?b1, k, key_cs, pub);
    //@ if (!b1) open [_]item_constraints_no_collision(k, key_cs, pub);
    check_valid_symmetric_key_item_size(key->size);
    //@ assert key_size == GCM_KEY_SIZE + 1;
    //@ chars_limits(key_cont);
    //@ chars_split(key_cont, 1);
    //@ assert chars(key_cont + 1, GCM_KEY_SIZE, ?key_cs0);
    //@ polarssl_cryptogram key_cg = polarssl_symmetric_key(principal2, count2);
    //@ close exists(key_cg);
    if (gcm_init(&gcm_context, POLARSSL_AES_CIPHER_ID, (key->content + 1), 
                (unsigned int) GCM_KEY_SIZE * 8) != 0) 
      abort_crypto_lib("Init gcm failed");
    //@ close item(key, k, pub);

    //@ open item(item, enc, pub);
    //@ assert item->content |-> ?i_cont &*& item->size |-> ?i_size;
    //@ close [1/2]hide_chars(i_cont, i_size, ?cs);
    //@ chars_limits(i_cont);
    //@ open [_]item_constraints(?b2, enc, cs, pub);
    //@ assert true == well_formed(cs, nat_length(cs));
    check_valid_symmetric_encrypted_item_size(item->size);
    //@ assert length(cs) > 1 + GCM_ENT_SIZE;

    int size = item->size - 1 - GCM_ENT_SIZE;
    //@ chars_split(i_cont, 1);
    tag = item->content + 1;
    //@ chars_split(tag, GCM_TAG_SIZE);
    memcpy(tag_buffer, tag, GCM_TAG_SIZE);
    iv = tag + GCM_TAG_SIZE;
    //@ chars_split(iv, GCM_IV_SIZE);
    memcpy(iv_buffer, iv, GCM_IV_SIZE);
    encrypted = iv + GCM_IV_SIZE;
    //@ assert [1/2]chars(tag, GCM_TAG_SIZE, ?tag_cs);
    //@ assert [1/2]chars(iv, GCM_IV_SIZE, ?iv_cs);
    //@ assert [1/2]chars(encrypted, size, ?enc_cs);
    //@ list<char> ent1 = append(tag_cs, iv_cs);
    //@ append_assoc(tag_cs, iv_cs, enc_cs);
    //@ take_append(GCM_ENT_SIZE, ent1, enc_cs);
    //@ drop_append(GCM_ENT_SIZE, ent1, enc_cs);
  
    if (size < POLARSSL_MIN_ENCRYPTED_BYTE_SIZE) 
      abort_crypto_lib("Gcm encryption failed: incorrect sizes");
    
    result->size = size;
    result->content = malloc(size);
    //@ assert result->content |-> ?r_cont;
    
    if (result->content == 0) abort_crypto_lib("Malloc failed");
  
    if (gcm_auth_decrypt(&gcm_context, (unsigned int) size, 
                         iv_buffer, GCM_IV_SIZE, NULL, 0, 
                         tag_buffer, GCM_TAG_SIZE,
                         encrypted, result->content) != 0)
      abort_crypto_lib("Gcm decryption failed");
    //@ assert chars(r_cont, size, ?dec_cs);
    /*@ polarssl_cryptogram cg1 = polarssl_auth_encrypted(
                                 principal2, count2, tag_cs, dec_cs, iv_cs); @*/
    //@ assert enc_cs == polarssl_chars_for_cryptogram(cg1);
    
    parse_item(result->content, size);
    //@ assert true == well_formed(dec_cs, nat_length(dec_cs));
    
    //@ chars_join(iv);
    //@ chars_join(tag);
    //@ chars_join(i_cont);
    //@ open [1/2]hide_chars(i_cont, i_size, cs);
    //@ assert chars(i_cont, i_size, cs);
    /*@ if (collision_in_run())
        {
          item r = dummy_item_for_tag(head(dec_cs));
          well_formed_valid_tag(dec_cs, nat_length(dec_cs));
          tag_for_dummy_item(r, head(dec_cs));
          collision_public(pub, dec_cs);
          close item_constraints(true, r, dec_cs, pub);
          leak item_constraints(true, r, dec_cs, pub);
          close item(result, r, pub);         
        }
        else
        {
          open item_constraints_no_collision(enc, cs, pub);
          assert [_]symmetric_encryption_entropy(enc)(?tag0, ?iv0);
          list<char> ent2 = append(tag0, iv0);
          assert take(GCM_ENT_SIZE, ent) == ent1;
          assert drop(GCM_ENT_SIZE, ent) == cons(length(tag0), ent2);
          assert cs == cons('i', ?cs0);
          assert cs0 == append(ent1, enc_cs);
          assert drop(GCM_ENT_SIZE, cs0) == enc_cs;
          switch(pay)
          {
            case some(pay1):
              assert [_]well_formed_item_chars(enc)(?cs_pay0);
              assert [_]item_constraints_no_collision(pay1, cs_pay0, pub);
              polarssl_cryptogram cg2 = polarssl_auth_encrypted(
                                        principal1, count1, tag0, cs_pay0, iv0);
              assert enc_cs == polarssl_chars_for_cryptogram(cg2);
              polarssl_chars_for_cryptogram_injective(cg1, cg2);
              close item_constraints(false, pay1, cs_pay0, pub);
              leak item_constraints(false, pay1, cs_pay0, pub);
              close item(result, pay1, pub);
            case none:
              open [_]ill_formed_item_chars(enc)(?cs_pay0);
              polarssl_cryptogram cg2 = polarssl_auth_encrypted(
                                        principal1, count1, tag0, cs_pay0, iv0);
              polarssl_chars_for_cryptogram_injective(cg1, cg2);
              assert cs_pay0 == dec_cs;
              
              retreive_proof_obligations();
              polarssl_generated_public_cryptograms_subset(polarssl_pub(pub), 
                                                           cs_pay0);
              deserialize_item(cs_pay0, pub);
              leak proof_obligations(pub);
              
              assert [_]item_constraints_no_collision(?pay1, cs_pay0, pub); 
              item_constraints_no_collision_well_formed(pay1, pay1);
              open  [_]well_formed_item_chars(pay1)(cs);
              assert false;
          }
        }
    @*/
    //@ close item(item, enc, pub);
    gcm_free(&gcm_context);
    //@ open gcm_context(&gcm_context);
  }
    
  debug_print("DECRYPTING RESULT:\n");
  print_item(result);
  
  return result;
}

