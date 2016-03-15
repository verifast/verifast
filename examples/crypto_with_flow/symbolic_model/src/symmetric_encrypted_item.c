#include "symmetric_encrypted_item.h"

#include "item_constraints.h"
#include "key_item.h"
#include "principal_ids.h"
#include "serialization.h"
#include "deserialization.h"

#include <string.h>

bool is_symmetric_encrypted(struct item *item)
  //@ requires [?f]world(?pub, ?key_clsfy) &*& item(item, ?i, pub);
  /*@ ensures  [f]world(pub, key_clsfy) &*& item(item, i, pub) &*&
               result ? i == symmetric_encrypted_item(_, _, _, _) : true; @*/
{
  //@ open [f]world(pub, key_clsfy);
  //@ open item(item, i, pub);
  //@ open [_]item_constraints(i, ?cs, pub);
  return item_tag(item->content, item->size) == TAG_SYMMETRIC_ENC;
  //@ close item(item, i, pub);
  //@ close [f]world(pub, key_clsfy);
}

void check_is_symmetric_encrypted(struct item *item)
  //@ requires [?f]world(?pub, ?key_clsfy) &*& item(item, ?i, pub);
  /*@ ensures  [f]world(pub, key_clsfy) &*& item(item, i, pub) &*&
               i == symmetric_encrypted_item(_, _, _, _); @*/
{
  if (!is_symmetric_encrypted(item))
    abort_crypto_lib("Presented item is not an encrypted item");
}

struct item *symmetric_encryption(struct item *key, struct item *payload)
  /*@ requires [?f]world(?pub, ?key_clsfy) &*&
               principal(?principal1, ?count1) &*&
                 [_]pub(nonce_item(principal1, count1 + 1, 0)) &*&
               item(payload, ?pay, pub) &*& item(key, ?k, pub) &*&
                 k == symmetric_key_item(?principal2, ?count2); @*/
  /*@ ensures  [f]world(pub, key_clsfy) &*&
               principal(principal1, count1 + 2) &*&
               item(payload, pay, pub) &*& item(key, k, pub) &*&
               item(result, ?enc, pub) &*&
               col ? true :
                 enc == symmetric_encrypted_item(principal2, count2,
                                                 some(pay), ?ent); @*/
{
  //@ open [f]world(pub, key_clsfy);
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
    char *encrypted;

    //@ open item(key, k, pub);
    //@ assert key->content |-> ?k_cont &*& key->size |-> ?k_size;
    check_valid_symmetric_key_item_size(key->size);
    //@ open [_]item_constraints(k, ?k_cs0, pub);
    //@ assert [_]ic_parts(k)(?k_tag, ?k_cs);
    //@ crypto_chars_limits(k_cont);
    //@ crypto_chars_split(k_cont, TAG_LENGTH);
    //@ WELL_FORMED(k_tag, k_cs, TAG_SYMMETRIC_KEY)
    //@ assert crypto_chars(secret, k_cont, TAG_LENGTH, k_tag);
    //@ assert crypto_chars(secret, k_cont + TAG_LENGTH, GCM_KEY_SIZE, k_cs);
    //@ cryptogram k_cg = cg_symmetric_key(principal2, count2);
    //@ if (col) k_cg = chars_for_cg_sur(k_cs, tag_symmetric_key);
    //@ if (col) crypto_chars_to_chars(k_cont + TAG_LENGTH, GCM_KEY_SIZE);
    //@ if (col) public_chars_extract(k_cont + TAG_LENGTH, k_cg);
    //@ if (col) chars_to_secret_crypto_chars(k_cont + TAG_LENGTH, GCM_KEY_SIZE);
    //@ close cryptogram(k_cont + TAG_LENGTH, GCM_KEY_SIZE, k_cs, k_cg);
    //@ close gcm_context(&gcm_context);
    if (gcm_init(&gcm_context, POLARSSL_CIPHER_ID_AES, (key->content + TAG_LENGTH),
                (unsigned int) GCM_KEY_SIZE * 8) != 0)
      abort_crypto_lib("Init gcm failed");
    //@ assert gcm_context_initialized(&gcm_context, ?p, ?c);
    //@ assert col || (p == principal2 && c == count2);
    //@ open cryptogram(k_cont + TAG_LENGTH, GCM_KEY_SIZE, k_cs, k_cg);
    //@ crypto_chars_join(k_cont);
    //@ close item(key, k, pub);

    //@ open item(payload, pay, pub);
    //@ open [_]item_constraints(pay, ?pay_cs, pub);
    //@ assert payload->content |-> ?p_cont &*& payload->size |-> ?p_size;
    //@ crypto_chars_limits(p_cont);
    if (payload->size >= INT_MAX - TAG_LENGTH - GCM_IV_SIZE - GCM_MAC_SIZE ||
        payload->size < MINIMAL_STRING_SIZE)
      abort_crypto_lib("Gcm encryption failed: incorrect sizes");
    result->size = TAG_LENGTH + GCM_IV_SIZE + GCM_MAC_SIZE + payload->size;
    result->content = malloc(result->size);

    //@ assert result->content |-> ?r_cont &*& result->size |-> ?r_size;
    if (result->content == 0)
      abort_crypto_lib("Malloc failed");
    //@ chars_split(r_cont, TAG_LENGTH);
    write_tag(result->content, TAG_SYMMETRIC_ENC);
    //@ assert chars(r_cont, TAG_LENGTH, ?tag_cs);
    //@ public_chars(r_cont, TAG_LENGTH);
    //@ assert tag_cs == full_tag(TAG_SYMMETRIC_ENC);
    //@ assert chars(r_cont + TAG_LENGTH, GCM_IV_SIZE + p_size, _);
    //@ chars_split(r_cont + TAG_LENGTH, GCM_IV_SIZE);
    iv = result->content + TAG_LENGTH;
    //@ close nonce_request(principal1, 0);
    //@ close [f]world(pub, key_clsfy);
    create_havege_random(iv, GCM_IV_SIZE);
    //@ open cryptogram(iv, GCM_IV_SIZE, ?iv_cs, ?iv_cg);
    memcpy(iv_buffer, iv, GCM_IV_SIZE);
    //@ close cryptogram(iv, GCM_IV_SIZE, iv_cs, iv_cg);
    //@ close polarssl_pub(pub)(iv_cg);
    //@ leak polarssl_pub(pub)(iv_cg);
    //@ public_cryptogram(iv, iv_cg);
    //@ public_chars(iv, GCM_IV_SIZE);
    encrypted = iv + GCM_IV_SIZE;
    //@ chars_split(encrypted, GCM_MAC_SIZE);
    //@ open principal(principal1, count1 + 1);
    if (gcm_crypt_and_tag(&gcm_context, GCM_ENCRYPT,
                          (unsigned int) payload->size, iv_buffer, 
                          GCM_IV_SIZE, NULL, 0, payload->content, 
                          encrypted + GCM_MAC_SIZE,
                          GCM_MAC_SIZE, encrypted) != 0)
      abort_crypto_lib("Gcm encryption failed");
    //@ close principal(principal1, count1 + 2);
    zeroize(iv_buffer, GCM_IV_SIZE);
    //@ assert crypto_chars(secret, encrypted, GCM_MAC_SIZE, ?mac_cs);
    //@ assert crypto_chars(secret, encrypted + GCM_MAC_SIZE, p_size, ?enc_cs);
    //@ crypto_chars_join(encrypted);
    //@ assert exists(?enc_cg);
    //@ list<char> cg_cs = append(mac_cs, enc_cs);
    //@ assert cg_cs == chars_for_cg(enc_cg);
    //@ list<char> cont_cs = append(iv_cs, cg_cs);
    //@ take_append(GCM_IV_SIZE, iv_cs, cg_cs);
    //@ drop_append(GCM_IV_SIZE, iv_cs, cg_cs);
    //@ list<char> cs = append(tag_cs, cont_cs);
    //@ take_append(TAG_LENGTH, tag_cs, cont_cs);
    //@ drop_append(TAG_LENGTH, tag_cs, cont_cs);
    
    //@ item enc;
    //@ list<char> ent = append(iv_cs, iv_cs);
    //@ take_append(GCM_IV_SIZE, iv_cs, iv_cs);
    //@ drop_append(GCM_IV_SIZE, iv_cs, iv_cs);
    /*@ if (col)
        {
          enc_cg = chars_for_cg_sur(cg_cs, tag_auth_encrypted);
          assert enc_cg == cg_auth_encrypted(?p0, ?c0, ?pay0, ?iv0);
          ent = append(iv_cs, iv0);
          take_append(GCM_IV_SIZE, iv_cs, iv0);
          drop_append(GCM_IV_SIZE, iv_cs, iv0);
          enc = symmetric_encrypted_item(p0, c0, some(pay), ent);
          public_chars(encrypted, GCM_MAC_SIZE + p_size);
          assert chars(encrypted, GCM_MAC_SIZE + p_size, cg_cs);
          chars_join(iv);
          chars_join(r_cont);
          assert chars(r_cont, r_size, cs);
          public_chars(r_cont, r_size);
          public_generated_split(polarssl_pub(pub), cs, TAG_LENGTH);
          close ic_sym_enc(enc)(iv0, cg_cs);
        }
        else
        {
          assert enc_cg == cg_auth_encrypted(principal2, count2, pay_cs, iv_cs);
          enc = symmetric_encrypted_item(principal2, count2, some(pay), ent);
          close polarssl_pub(pub)(cg_nonce(principal1, count1 + 1));
          leak  polarssl_pub(pub)(cg_nonce(principal1, count1 + 1));
          public_generated(polarssl_pub(pub), cg_nonce(principal1, count1 + 1));
          chars_to_secret_crypto_chars(iv, GCM_IV_SIZE);
          crypto_chars_join(iv);
          chars_to_secret_crypto_chars(r_cont, TAG_LENGTH);
          crypto_chars_join(r_cont);
          assert crypto_chars(secret, r_cont, r_size, cs);
          close ic_sym_enc(enc)(iv_cs, cg_cs);
        }
    @*/
    //@ well_formed_item_constraints(pay, enc);
    //@ close ic_cg(enc)(cg_cs, enc_cg);
    //@ close ic_parts(enc)(tag_cs, cont_cs);
    //@ WELL_FORMED(tag_cs, cont_cs, TAG_SYMMETRIC_ENC)
    //@ close item_constraints(enc, cs, pub);
    //@ leak item_constraints(enc, cs, pub);
    //@ close item(result, enc, pub);
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
  //@ ensures  size > TAG_LENGTH + GCM_IV_SIZE;
{
  if (size <= TAG_LENGTH + GCM_KEY_SIZE)
    abort_crypto_lib("Illegal size for symmetric encrypted item");
}

struct item *symmetric_decryption(struct item *key, struct item *item)
  /*@ requires [?f]world(?pub, ?key_clsfy) &*&
               item(item, ?enc, pub) &*&
                 enc == symmetric_encrypted_item(?principal1, ?count1,
                                                 ?pay, ?ent) &*&
               item(key, ?k, pub) &*&
                 k == symmetric_key_item(?principal2, ?count2); @*/
  /*@ ensures  [f]world(pub, key_clsfy) &*&
               item(item, enc, pub) &*& item(key, k, pub) &*&
               item(result, ?dec, pub) &*&
               col ? [_]pub(dec) :
               switch(pay)
               {
                 case some(dec2):
                   return principal1 == principal2 &&
                          count1 == count2 && dec == dec2;
                 case none:
                   return false;
               }; @*/
{
  debug_print("DECRYPTING:\n");
  print_item(item);
  check_is_symmetric_encrypted(item);

  //@ open [f]world(pub, key_clsfy);
  struct item* result;
  result = malloc(sizeof(struct item));
  if (result == 0) abort_crypto_lib("Malloc failed");

  {
    gcm_context gcm_context;
    char *iv;
    char iv_buffer[GCM_IV_SIZE];
    char *encrypted;

    //@ open item(key, k, pub);
    //@ assert key->content |-> ?k_cont &*& key->size |-> ?k_size;
    check_valid_symmetric_key_item_size(key->size);
    //@ open [_]item_constraints(k, ?k_cs0, pub);
    //@ assert [_]ic_parts(k)(?k_tag, ?k_cs);
    //@ crypto_chars_limits(k_cont);
    //@ crypto_chars_split(k_cont, TAG_LENGTH);
    //@ WELL_FORMED(k_tag, k_cs, TAG_SYMMETRIC_KEY)
    //@ assert crypto_chars(secret, k_cont, TAG_LENGTH, k_tag);
    //@ assert crypto_chars(secret, k_cont + TAG_LENGTH, GCM_KEY_SIZE, k_cs);
    //@ cryptogram k_cg = cg_symmetric_key(principal2, count2);
    //@ if (col) k_cg = chars_for_cg_sur(k_cs, tag_symmetric_key);
    //@ if (col) crypto_chars_to_chars(k_cont + TAG_LENGTH, GCM_KEY_SIZE);
    //@ if (col) public_chars_extract(k_cont + TAG_LENGTH, k_cg);
    //@ if (col) chars_to_secret_crypto_chars(k_cont + TAG_LENGTH, GCM_KEY_SIZE);
    //@ close cryptogram(k_cont + TAG_LENGTH, GCM_KEY_SIZE, k_cs, k_cg);
    //@ close gcm_context(&gcm_context);
    if (gcm_init(&gcm_context, POLARSSL_CIPHER_ID_AES, (key->content + TAG_LENGTH),
                (unsigned int) GCM_KEY_SIZE * 8) != 0)
      abort_crypto_lib("Init gcm failed");
    //@ assert gcm_context_initialized(&gcm_context, ?p, ?c);
    //@ assert col || (p == principal2 && c == count2);
    //@ open cryptogram(k_cont + TAG_LENGTH, GCM_KEY_SIZE, k_cs, k_cg);
    //@ crypto_chars_join(k_cont);
    //@ close item(key, k, pub);

    //@ open item(item, enc, pub);
    //@ assert item->content |-> ?i_cont &*& item->size |-> ?i_size;
    //@ open [_]item_constraints(enc, ?cs, pub);
    //@ open [_]ic_parts(enc)(?enc_tag, ?enc_cont);
    //@ open [_]ic_cg(enc)(_, ?enc_cg);
    //@ take_append(TAG_LENGTH, enc_tag, enc_cont);
    //@ drop_append(TAG_LENGTH, enc_tag, enc_cont);
    //@ open [_]ic_sym_enc(enc)(?enc_iv, ?cg_cs);
    //@ assert true == well_formed(cs, nat_length(cs));
    //@ close [1/2]hide_crypto_chars(_, i_cont, i_size, cs);
    check_valid_symmetric_encrypted_item_size(item->size);
    //@ assert length(cs) > TAG_LENGTH + GCM_IV_SIZE;
    int size = item->size - TAG_LENGTH - GCM_IV_SIZE - GCM_MAC_SIZE;
    if (size <= MINIMAL_STRING_SIZE) abort_crypto_lib("Gcm decryption failed");
    //@ crypto_chars_limits(i_cont);
    //@ crypto_chars_split(i_cont, TAG_LENGTH);
    iv = item->content + TAG_LENGTH;
    //@ crypto_chars_split(iv, GCM_IV_SIZE);
    //@ assert [1/2]crypto_chars(secret, iv, GCM_IV_SIZE, ?iv_cs);
    memcpy(iv_buffer, iv, GCM_IV_SIZE);
    //@ assert cs == append(enc_tag, enc_cont);
    //@ assert enc_cont == append(iv_cs, cg_cs);
    //@ public_crypto_chars(iv, GCM_IV_SIZE);
    //@ chars_to_secret_crypto_chars(iv, GCM_IV_SIZE);
    encrypted = iv + GCM_IV_SIZE;
    //@ crypto_chars_limits(encrypted);
    //@ crypto_chars_split(encrypted, GCM_MAC_SIZE);
    //@ assert [1/2]crypto_chars(secret, encrypted, GCM_MAC_SIZE, ?mac_cs);
    /*@ assert [1/2]crypto_chars(secret, encrypted + GCM_MAC_SIZE, 
                                 size, ?enc_cs); @*/
    //@ assert cg_cs == append(mac_cs, enc_cs);                             
    result->size = size;
    result->content = malloc(size);
    if (result->content == 0) abort_crypto_lib("Malloc failed");
    //@ assert result->content |-> ?r_cont &*& result->size |-> size;
    //@ if (col) enc_cg = chars_for_cg_sur(cg_cs, tag_auth_encrypted);
    //@ close exists(enc_cg);
    if (gcm_auth_decrypt(&gcm_context, (unsigned int) size,
                         iv_buffer, GCM_IV_SIZE, NULL, 0, encrypted, 
                         GCM_MAC_SIZE, encrypted + GCM_MAC_SIZE,
                         result->content) != 0)
      abort_crypto_lib("Gcm decryption failed");
    //@ assert crypto_chars(secret, r_cont, size, ?dec_cs);
    //@ assert col || enc_cg == cg_auth_encrypted(principal1, count1, dec_cs, iv_cs);
    //@ crypto_chars_join(encrypted);
    //@ crypto_chars_join(iv);
    //@ crypto_chars_join(i_cont);
    //@ open [1/2]hide_crypto_chars(_, i_cont, i_size, cs);
    //@ close item(item, enc, pub);
    gcm_free(&gcm_context);
    //@ open gcm_context(&gcm_context);
    zeroize(iv_buffer, GCM_IV_SIZE);
    //@ close [f]world(pub, key_clsfy);
    
    /*@ if (col)
        {
          crypto_chars_to_chars(r_cont, size);
          chars_to_crypto_chars(r_cont, size);
        }
        else
        {
          assert enc == symmetric_encrypted_item(principal1, count1,
                                                 pay, ent);
          assert enc_cg == cg_auth_encrypted(principal1, count1, 
                                             dec_cs, enc_iv);
          switch(pay)
          {
            case some(pay1):
              assert [_]item_constraints(pay1, dec_cs, pub);
            case none:
              open [_]ill_formed_item_chars(enc)(dec_cs);
              assert [_]public_generated(polarssl_pub(pub))(dec_cs);
              public_crypto_chars(r_cont, size);
              chars_to_crypto_chars(r_cont, size);
          }
        }
    @*/
    parse_item(result->content, size);
    /*@ if (col)
        {
          public_chars(r_cont, size);
          chars_to_secret_crypto_chars(r_cont, size);
          retreive_proof_obligations();
          deserialize_item(dec_cs, pub);
          leak proof_obligations(pub);
        }
    @*/
    //@ assert crypto_chars(secret, r_cont, size, dec_cs);
    //@ assert [_]item_constraints(?r, dec_cs, pub);
    //@ close item(result, r, pub);
  }

  debug_print("DECRYPTING RESULT:\n");
  print_item(result);

  return result;
}
