#include "asymmetric_encrypted_item.h"

#include "item_constraints.h"
#include "key_item.h"
#include "principal_ids.h"
#include "serialization.h"
#include "deserialization.h"

#include <string.h>

bool is_asymmetric_encrypted(struct item *item)
  //@ requires [?f]world(?pub, ?key_clsfy) &*& item(item, ?i, pub);
  /*@ ensures  [f]world(pub, key_clsfy) &*& item(item, i, pub) &*&
               result ? i == asymmetric_encrypted_item(_, _, _, _) : true; @*/
{
  //@ open [f]world(pub, key_clsfy);
  //@ open item(item, i, pub);
  //@ open [_]item_constraints(i, ?cs, pub);
  return item_tag(item->content, item->size) == TAG_ASYMMETRIC_ENC;
  //@ close item(item, i, pub);
  //@ close [f]world(pub, key_clsfy);
}

void check_is_asymmetric_encrypted(struct item *item)
  //@ requires [?f]world(?pub, ?key_clsfy) &*& item(item, ?i, pub);
  /*@ ensures  [f]world(pub, key_clsfy) &*& item(item, i, pub) &*&
               i == asymmetric_encrypted_item(_, _, _, _); @*/
{
  if (!is_asymmetric_encrypted(item))
    abort_crypto_lib("Presented item is not an asymmetric encrypted item");
}

int asym_enc_havege_random_stub(void *havege_state, char *output, size_t len)
  /*@ requires [?f]havege_state_initialized(havege_state) &*&
               random_request(?principal, ?info, ?key_request) &*&
               random_permission(principal, ?count) &*&
               chars(output, len, _) &*& len >= MIN_RANDOM_SIZE;
  @*/
  /*@ ensures  [f]havege_state_initialized(havege_state) &*&
               random_permission(principal, count + 1) &*&
               result == 0 ?
                 cryptogram(output, len, ?cs, ?cg) &*&
                 info == cg_info(cg) &*&
                 key_request ?
                   cg == cg_symmetric_key(principal, count + 1)
                 :
                   cg == cg_nonce(principal, count + 1)
               :
                 chars(output, len, _);
  @*/
{
  return havege_random(havege_state, output, len);
}

struct item *asymmetric_encryption(struct item *key, struct item *payload)
  /*@ requires [?f]world(?pub, ?key_clsfy) &*&
               principal(?principal1, ?count1) &*&
               item(payload, ?pay, pub) &*& item(key, ?k, pub) &*&
               k == public_key_item(?principal2, ?count2); @*/
  /*@ ensures  [f]world(pub, key_clsfy) &*&
               principal(principal1, count1 + 1) &*&
               item(payload, pay, pub) &*& item(key, k, pub) &*&
               item(result, ?enc, pub) &*&
               col ? true :
                 enc == asymmetric_encrypted_item(principal2, count2,
                                                  some(pay), ?ent); @*/
{
  debug_print("ASYM ENCRYPTING:\n");
  print_item(payload);

  struct item* result;
  result = malloc(sizeof(struct item));
  if (result == 0) abort_crypto_lib("Malloc failed");

  {
    pk_context context;
    unsigned int olen;
    char output[MAX_PACKAGE_SIZE];

    // Key
    //@ close pk_context(&context);
    //@ open [f]world(pub, key_clsfy);
    pk_init(&context);
    //@ close [f]world(pub, key_clsfy);
    set_public_key(&context, key);
    //@ open [f]world(pub, key_clsfy);
    /*@ assert pk_context_with_key(&context, pk_public,
                                   ?principal, ?count, RSA_BIT_KEY_SIZE); @*/
    //@ assert col || principal == principal2;
    //@ assert col || count == count2;

    // Encryption
    //@ open item(payload, pay, pub);
    //@ assert [_]item_constraints(pay, ?pay_cs, pub);
    if (payload->size > RSA_KEY_SIZE)
      abort_crypto_lib("Asymmetric encryption failed: incorrect sizes");
    void *random_state = nonces_expose_state();
    //@ close random_state_predicate(havege_state_initialized);
    /*@ produce_function_pointer_chunk random_function(
                      asym_enc_havege_random_stub)
                     (havege_state_initialized)(state, out, len) { call(); } @*/
    //@ open principal(principal1, count1);
    if(pk_encrypt(&context, payload->content, (unsigned int) payload->size,
                  output, &olen, MAX_PACKAGE_SIZE,
                  asym_enc_havege_random_stub, random_state) != 0)
      abort_crypto_lib("Encryption failed");
    //@ close principal(principal1, count1 + 1);
    //@ open cryptogram(output, ?enc_length, ?enc_cs, ?enc_cg);
    //@ assert enc_cg == cg_asym_encrypted(principal, count, pay_cs, ?ent);
    //@ close exists(enc_cg);
    //@ assert u_integer(&olen, enc_length);
    //@ assert enc_length > 0 &*& enc_length < MAX_PACKAGE_SIZE;
    //@ assert enc_length > 0 &*& enc_length <= RSA_SERIALIZED_KEY_SIZE;
    nonces_hide_state(random_state);
    //@ pk_release_context_with_key(&context);
    pk_free(&context);
    //@ open pk_context(&context);
    //@ close [f]world(pub, key_clsfy);

    // Create item
    result->size = TAG_LENGTH + (int) olen;
    result->content = malloc(result->size);
    if (result->content == 0) {abort_crypto_lib("Malloc failed");}
    write_tag(result->content, TAG_ASYMMETRIC_ENC);
    //@ assert result->content |-> ?cont &*& result->size |-> ?size;
    if (olen < MINIMAL_STRING_SIZE) {abort_crypto_lib("Asymmetric encryption failed: to small");}
    memcpy(result->content + TAG_LENGTH, output, olen);
    //@ assert chars(cont, TAG_LENGTH, ?cs_tag);
    //@ public_chars(cont, TAG_LENGTH);
    //@ chars_to_secret_crypto_chars(cont, TAG_LENGTH);
    //@ assert cs_tag == full_tag(TAG_ASYMMETRIC_ENC);
    //@ crypto_chars_join(cont);

    //@ item enc = asymmetric_encrypted_item(principal, count, some(pay), ent);
    //@ list<char> cs = append(cs_tag, enc_cs);
    //@ WELL_FORMED(cs_tag, enc_cs, TAG_ASYMMETRIC_ENC)
    //@ close ic_parts(enc)(cs_tag, enc_cs);
    /*@ if (col)
      {
        crypto_chars_to_chars(cont, size);
        public_chars(cont, size);
        chars_to_secret_crypto_chars(cont, size);
        public_generated_split(polarssl_pub(pub), cs, TAG_LENGTH);
      }
    @*/
    //@ well_formed_item_constraints(pay, enc);
    //@ close item_constraints(enc, cs, pub);
    //@ leak item_constraints(enc, cs, pub);
    //@ close item(result, enc, pub);
    zeroize(output, (int) olen);
    //@ chars_join(output);
    //@ close item(payload, pay, pub);
  }

  debug_print("ENCRYPTING RESULT:\n");
  print_item(result);

  return result;
}

struct item *asymmetric_decryption(struct item *key, struct item *item, char tag)
  /*@ requires [?f]world(?pub, ?key_clsfy) &*& true == valid_tag(tag) &*&
               principal(?principal1, ?count1) &*&
               item(item, ?enc, pub) &*& item(key, ?k, pub) &*&
                 enc == asymmetric_encrypted_item(?principal2, ?count2,
                                                  ?pay, ?ent) &*&
               k == private_key_item(?principal3, ?count3); @*/
  /*@ ensures  [f]world(pub, key_clsfy) &*&
               principal(principal1, count1 + 1) &*&
               item(item, enc, pub) &*& item(key, k, pub) &*&
               item(result, ?dec, pub) &*& tag_for_item(dec) == tag &*&
               col ? 
                 [_]pub(dec) 
               : principal2 != principal3 || count2 != count3 ? 
                 true == key_clsfy(principal3, count3, false) &*& 
                 [_]pub(dec) 
               :
                 switch(pay)
                 {
                   case some(dec2):
                     return dec == dec2;
                   case none:
                     return false;
                 }; @*/
{
  struct item* result = 0;
  debug_print("DECRYPTING:\n");
  print_item(item);
  check_is_asymmetric_encrypted(item);

  {
    pk_context context;
    unsigned int olen;
    char output[MAX_PACKAGE_SIZE];

    // Key
    //@ close pk_context(&context);
    //@ open [f]world(pub, key_clsfy);
    pk_init(&context);
    //@ close [f]world(pub, key_clsfy);
    set_private_key(&context, key);
    //@ open [f]world(pub, key_clsfy);
    /*@ assert pk_context_with_key(&context, pk_private,
                                   ?principal, ?count, RSA_BIT_KEY_SIZE); @*/

    // Decryption
    //@ open item(item, enc, pub);
    /*@ assert enc == asymmetric_encrypted_item(principal2, count2,
                                                pay, ent); @*/
    //@ open [_]item_constraints(enc, ?enc_cs, pub);
    //@ assert [_]ic_parts(enc)(?enc_tag, ?enc_cont);
    //@ assert enc_cs == append(enc_tag, enc_cont);
    //@ open [_]exists(?enc_cg);
    //@ assert enc_cg == cg_asym_encrypted(principal2, count2, ?cs_pay, ent);
    if (item->size - TAG_LENGTH > RSA_KEY_SIZE ||
        item->size - TAG_LENGTH < MINIMAL_STRING_SIZE)
      abort_crypto_lib("Asymmetric decryption failed: incorrect sizes");
    //@ assert item->content |-> ?i_cont &*& item->size |-> ?i_size;
    //@ crypto_chars_split(i_cont, TAG_LENGTH);
    //@ drop_append(TAG_LENGTH, enc_tag, enc_cont);
    //@ assert crypto_chars(secret, i_cont + TAG_LENGTH, i_size - TAG_LENGTH, enc_cont);
    //@ if (col) enc_cg = chars_for_cg_sur(enc_cont, tag_asym_encrypted);
    //@ if (col) public_crypto_chars_extract(i_cont + TAG_LENGTH, enc_cg);
    //@ close cryptogram(i_cont + TAG_LENGTH, i_size - TAG_LENGTH, enc_cont, enc_cg);
    void *random_state = nonces_expose_state();
    //@ close random_state_predicate(havege_state_initialized);
    /*@ produce_function_pointer_chunk random_function(
                      asym_enc_havege_random_stub)
                     (havege_state_initialized)(state, out, len) { call(); } @*/
    //@ open principal(principal1, count1);
    //@ structure s = known_value(0, full_tag(tag));
    //@ close decryption_request(false, principal1, s, initial_request, enc_cont);
    if(pk_decrypt(&context, item->content + TAG_LENGTH,
                  (unsigned int) item->size - TAG_LENGTH,
                  output, &olen, MAX_PACKAGE_SIZE,
                  asym_enc_havege_random_stub, random_state) != 0)
      abort_crypto_lib("Decryption failed");
    /*@ open decryption_response(false, principal1, s, initial_request,
                                 ?wrong_key, ?p_key, ?c_key, ?cs_out); @*/
    //@ assert u_integer(&olen, ?size_out);
    //@ pk_release_context_with_key(&context);
    //@ open cryptogram(i_cont + TAG_LENGTH, i_size - TAG_LENGTH, enc_cont, enc_cg);
    pk_free(&context);
    //@ open pk_context(&context);
    nonces_hide_state(random_state);
    //@ assert chars((void*)output + size_out, MAX_PACKAGE_SIZE - size_out, ?cs_rest);
    result = malloc(sizeof(struct item));
    if (result == 0) {abort_crypto_lib("Malloc failed");}
    result->size = (int) olen;
    if ((int) olen <= MINIMAL_STRING_SIZE)
      abort_crypto_lib("Decryption: Incorrect size");
    result->content = malloc(result->size);
    if (result->content == 0) {abort_crypto_lib("Malloc failed");}
    //@ assert u_integer(&olen, ?olen_val);
    //@ assert crypto_chars(?kind, output, olen_val, cs_out);
    //@ close [f]world(pub, key_clsfy);
    //@ close check_tag2_ghost_args(false, wrong_key, p_key, c_key);
    check_tag2(output, tag);
    //@ switch(kind){case normal: case secret:}
    memcpy(result->content, output, olen);
    //@ assert result->content |-> ?cont;
    //@ assert crypto_chars(kind, cont, olen_val, cs_out);
    zeroize(output, (int) olen);
    //@ chars_join(output);
    //@ close item(item, enc, pub);
    //@ assert enc == asymmetric_encrypted_item(principal2, count2, pay, ent);
    //@ assert col || enc_cg == cg_asym_encrypted(principal2, count2, cs_pay, ent);
    /*@ if (col)
        {
          crypto_chars_to_chars(cont, olen_val);
          public_chars(cont, olen_val);
          chars_to_crypto_chars(cont, olen_val);
        }
        else if (wrong_key)
        {
          assert true == key_clsfy(principal3, count3, false);
          public_chars(cont, olen_val);
          chars_to_crypto_chars(cont, olen_val);
        }
        else
        {
          assert principal2 == principal3;
          assert count2 == count3;
          assert cs_out == cs_pay;
          switch(pay)
          {
            case some(pay1):
              assert [_]item_constraints(pay1, cs_out, pub);
            case none:
              open [_]ill_formed_item_chars(enc)(cs_out);
              assert [_]public_generated(polarssl_pub(pub))(cs_out);
              public_crypto_chars(cont, olen_val);
              chars_to_crypto_chars(cont, olen_val);
          }
        }
    @*/
    parse_item(result->content, (int) olen);
    /*@ if (col || wrong_key)
        {
          retreive_proof_obligations();
          deserialize_item(cs_out, pub);
          leak proof_obligations(pub);
          chars_to_secret_crypto_chars(cont, olen_val);
        }
    @*/
    //@ open [_]item_constraints(?dec, cs_out, pub);
    //@ assert [_]ic_parts(dec)(?dec_tag, ?dec_cont);
    //@ take_append(TAG_LENGTH, dec_tag, dec_cont);
    //@ drop_append(TAG_LENGTH, dec_tag, dec_cont);
    //@ assert dec_tag == full_tag(tag);
    //@ assert tag_for_item(dec) == tag;
    //@ close item(result, dec, pub);
  }
  return result;
}

