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
               chars_(output, len, _) &*& len >= MIN_RANDOM_SIZE;
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
                 chars_(output, len, _);
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
    size_t olen;
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
    //@ assert [_]item_constraints(pay, ?pay_ccs, pub);
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
    //@ open cryptogram(output, ?enc_length, ?enc_ccs, ?enc_cg);
    //@ assert enc_cg == cg_rsa_encrypted(principal, count, pay_ccs, ?ent);
    //@ assert olen |-> enc_length;
    //@ assert enc_length > 0 &*& enc_length < MAX_PACKAGE_SIZE;
    //@ assert enc_length > 0 &*& enc_length <= RSA_SERIALIZED_KEY_SIZE;
    nonces_hide_state(random_state);
    //@ pk_release_context_with_key(&context);
    pk_free(&context);
    //@ open pk_context(&context);
    //@ close [f]world(pub, key_clsfy);

    // Create item
    result->size = TAG_LENGTH + (int) olen;
    result->content = malloc((size_t)result->size);
    if (result->content == 0) {abort_crypto_lib("Malloc failed");}
    write_tag(result->content, TAG_ASYMMETRIC_ENC);
    //@ assert result->content |-> ?cont &*& result->size |-> ?size;
    if (olen < MINIMAL_STRING_SIZE) {abort_crypto_lib("Asymmetric encryption failed: to small");}
    crypto_memcpy(result->content + TAG_LENGTH, output, olen);

    //@ item enc = asymmetric_encrypted_item(principal, count, some(pay), ent);
    //@ close ic_cg(enc)(enc_ccs, enc_cg);
    //@ well_formed_item_constraints(pay, enc);
    //@ CLOSE_ITEM_CONSTRAINTS(cont, TAG_ASYMMETRIC_ENC, size, enc)
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
    size_t olen;
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
    //@ assert [_]item_constraints(enc, ?enc_ccs, pub);
    //@ OPEN_ITEM_CONSTRAINTS(enc, enc_ccs, pub)
    //@ assert [_]ic_parts(enc)(?enc_tag, ?enc_cont);
    //@ open [_]ic_cg(enc)(_, ?enc_cg);
    //@ assert enc_cg == cg_rsa_encrypted(principal2, count2, ?ccs_pay, ent);
    if (item->size - TAG_LENGTH > RSA_KEY_SIZE ||
        item->size - TAG_LENGTH < MINIMAL_STRING_SIZE)
      abort_crypto_lib("Asymmetric decryption failed: incorrect sizes");
    //@ assert item->content |-> ?i_cont &*& item->size |-> ?i_size;
    //@ crypto_chars_split(i_cont, TAG_LENGTH);
    //@ drop_append(TAG_LENGTH, enc_tag, enc_cont);
    //@ assert crypto_chars(secret, i_cont + TAG_LENGTH, i_size - TAG_LENGTH, enc_cont);
    //@ if (col) enc_cg = ccs_for_cg_sur(enc_cont, tag_asym_encrypted);
    //@ if (col) public_ccs_cg(enc_cg);
    //@ close cryptogram(i_cont + TAG_LENGTH, i_size - TAG_LENGTH, enc_cont, enc_cg);
    void *random_state = nonces_expose_state();
    //@ close random_state_predicate(havege_state_initialized);
    /*@ produce_function_pointer_chunk random_function(
                      asym_enc_havege_random_stub)
                     (havege_state_initialized)(state, out, len) { call(); } @*/
    //@ open principal(principal1, count1);
    //@ structure s = known_value(0, full_ctag(c_to_cc(tag)));
    //@ close decryption_pre(false, false, principal1, s, enc_cont);
    if(pk_decrypt(&context, item->content + TAG_LENGTH,
                  (unsigned int) item->size - TAG_LENGTH,
                  output, &olen, MAX_PACKAGE_SIZE,
                  asym_enc_havege_random_stub, random_state) != 0)
      abort_crypto_lib("Decryption failed");
    /*@ open decryption_post(false, ?garbage, principal1,
                             s, ?p_key, ?c_key, ?ccs_out); @*/
    //@ assert olen |-> ?size_out;
    //@ pk_release_context_with_key(&context);
    //@ open cryptogram(i_cont + TAG_LENGTH, i_size - TAG_LENGTH, enc_cont, enc_cg);
    pk_free(&context);
    //@ open pk_context(&context);
    nonces_hide_state(random_state);
    //@ assert chars_((void*)output + size_out, MAX_PACKAGE_SIZE - size_out, ?ccs_rest);
    result = malloc(sizeof(struct item));
    if (result == 0) {abort_crypto_lib("Malloc failed");}
    result->size = (int) olen;
    if ((int) olen <= MINIMAL_STRING_SIZE)
      abort_crypto_lib("Decryption: Incorrect size");
    result->content = malloc((size_t)result->size);
    if (result->content == 0) {abort_crypto_lib("Malloc failed");}
    //@ close [f]world(pub, key_clsfy);
    //@ assert olen |-> ?olen_val;
    //@ assert crypto_chars(_, output, olen_val, ccs_out);
    //@ crypto_chars_split(output, TAG_LENGTH);
    //@ assert crypto_chars(_, output, TAG_LENGTH, ?ccs_tag);
    //@ assert crypto_chars(_, (void*) output + TAG_LENGTH, olen_val - TAG_LENGTH, ?ccs_i);
    /*@ if (col)
        {
          crypto_chars_to_chars(output, TAG_LENGTH);
          chars_to_crypto_chars(output, TAG_LENGTH);
        }
        else if (!garbage)
        {
          switch(pay)
          {
            case some(pay1):
              OPEN_ITEM_CONSTRAINTS(pay1, ccs_out, pub)
            case none:
              open [_]ill_formed_item_ccs(enc)(ccs_out);
              public_ccs_split(ccs_out, TAG_LENGTH);
          }
          public_crypto_chars(output, TAG_LENGTH);
          chars_to_crypto_chars(output, TAG_LENGTH);
        }
    @*/
    //@ close check_tag2_args(false, garbage, principal1, p_key, c_key, ccs_i);
    check_tag2(output, tag);
    /*@ if (!garbage) 
        {
          crypto_chars_to_chars(output, TAG_LENGTH);
          chars_to_secret_crypto_chars(output, TAG_LENGTH);
        }
    @*/
    //@ crypto_chars_join(output);
    crypto_memcpy(result->content, output, olen);
    //@ assert result->content |-> ?cont;
    //@ assert crypto_chars(?kind, cont, olen_val, ccs_out);
    zeroize(output, (int) olen);
    //@ close item(item, enc, pub);
    //@ assert enc == asymmetric_encrypted_item(principal2, count2, pay, ent);
    //@ assert col || enc_cg == cg_rsa_encrypted(principal2, count2, ccs_pay, ent);
    
    /*@ if (col || garbage)
        {
          crypto_chars_to_chars(cont, olen_val);
          public_chars(cont, olen_val);
          chars_to_crypto_chars(cont, olen_val);
          assert col || key_clsfy(principal3, count3, false);
        }
        else
        {
          assert principal2 == principal3;
          assert count2 == count3;
          assert ccs_out == ccs_pay;
          switch(pay)
          {
            case some(pay1):
              assert [_]item_constraints(pay1, ccs_out, pub);
            case none:
              open [_]ill_formed_item_ccs(enc)(ccs_out);
              assert [_]public_ccs(ccs_out);
              public_crypto_chars(cont, olen_val);
              chars_to_crypto_chars(cont, olen_val);
          }
        }
    @*/
    parse_item(result->content, (int) olen);
    /*@ if (col || garbage)
        {
          retreive_proof_obligations();
          deserialize_item(ccs_out);
          leak proof_obligations(pub);
          crypto_chars_to_chars(cont, olen_val);
          chars_to_secret_crypto_chars(cont, olen_val);
        }
    @*/
    //@ assert [_]item_constraints(?dec, ccs_out, pub);
    //@ OPEN_ITEM_CONSTRAINTS(dec, ccs_out, pub)
    //@ assert [_]ic_parts(dec)(?dec_tag, ?dec_cont); 
    //@ close item(result, dec, pub);
    //@ c_to_cc_inj(tag, tag_for_item(dec));
  }
  return result;
}

