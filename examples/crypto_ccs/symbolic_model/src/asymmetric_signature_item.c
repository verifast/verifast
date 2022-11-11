#include "asymmetric_signature_item.h"

#include "item_constraints.h"
#include "key_item.h"
#include "principal_ids.h"
#include "serialization.h"
#include "deserialization.h"

#include <string.h>

bool is_asymmetric_signature(struct item *item)
  //@ requires [?f]world(?pub, ?key_clsfy) &*& item(item, ?i, pub);
  /*@ ensures  [f]world(pub, key_clsfy) &*& item(item, i, pub) &*&
               result ? i == asymmetric_signature_item(_, _, _, _) : true; @*/
{
  //@ open [f]world(pub, key_clsfy);
  //@ open item(item, i, pub);
  //@ open [_]item_constraints(i, ?cs, pub);
  return item_tag(item->content, item->size) == TAG_ASYMMETRIC_SIG;
  //@ close item(item, i, pub);
  //@ close [f]world(pub, key_clsfy);
}

void check_is_asymmetric_signature(struct item *item)
  //@ requires [?f]world(?pub, ?key_clsfy) &*& item(item, ?i, pub);
  /*@ ensures  [f]world(pub, key_clsfy) &*& item(item, i, pub) &*&
               i == asymmetric_signature_item(_, _, _, _); @*/
{
  if (!is_asymmetric_signature(item))
    abort_crypto_lib("Presented item is not an asymmetric signature item");
}

int asym_sig_havege_random_stub(void *havege_state, char *output, size_t len)
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

struct item *asymmetric_signature(struct item *key, struct item *payload)
  /*@ requires [?f]world(?pub, ?key_clsfy) &*&
               principal(?principal1, ?count1) &*&
               item(payload, ?pay, pub) &*& item(key, ?k, pub) &*&
               k == private_key_item(?principal2, ?count2); @*/
  /*@ ensures  [f]world(pub, key_clsfy) &*&
               principal(principal1, count1 + 1) &*&
               item(payload, pay, pub) &*& item(key, k, pub) &*&
               item(result, ?sig, pub) &*&
               col ? true :
                 sig == asymmetric_signature_item(principal2, count2,
                                                  some(pay), ?ent); @*/
{
  debug_print("ASYM SIGNING:\n");
  print_item(payload);

  struct item* result;
  result = malloc(sizeof(struct item));
  if (result == 0) abort_crypto_lib("Malloc failed");

  debug_print("signing item\n");
  print_item(payload);
  print_item(key);

  {
    pk_context context;
    size_t olen;
    char* output;

    // Key
    //@ close pk_context(&context);
    //@ open [f]world(pub, key_clsfy);
    pk_init(&context);
    //@ close [f]world(pub, key_clsfy);
    set_private_key(&context, key);
    //@ open [f]world(pub, key_clsfy);
    /*@ assert pk_context_with_key(&context, pk_private,
                                   ?principal, ?count, RSA_BIT_KEY_SIZE); @*/
    //@ assert col || principal == principal2;
    //@ assert col || count == count2;

    // Payload
    //@ open item(payload, pay, pub);
    //@ open [_]item_constraints(pay, ?pay_ccs, pub);
    //@ assert payload->content |-> ?p_cont &*& payload->size |-> ?p_size;
    if (payload->size > RSA_KEY_SIZE)
      abort_crypto_lib("Assymetric signing failed: incorrect size");
    output = malloc(RSA_KEY_SIZE);
    if (output == 0) abort_crypto_lib("Malloc failed");

    void *random_state = nonces_expose_state();
    //@ close random_state_predicate(havege_state_initialized);
    /*@ produce_function_pointer_chunk random_function(
                      asym_sig_havege_random_stub)
                     (havege_state_initialized)(state, out, len) { call(); } @*/
    //@ open principal(principal1, count1);
    if(pk_sign(&context, MBEDTLS_MD_NONE,
               payload->content, (unsigned int) payload->size,
               output, &olen,
               asym_sig_havege_random_stub, random_state) != 0)
      abort_crypto_lib("Signing failed");
    //@ open principal(principal1, count1 + 1);
    //@ open cryptogram(output, ?sig_length, ?sig_ccs, ?sig_cg);
    //@ assert sig_cg == cg_rsa_signature(principal, count, pay_ccs, ?ent);
    //@ assert olen |-> sig_length;
    //@ assert sig_length > 0 &*& sig_length <= RSA_KEY_SIZE;
    nonces_hide_state(random_state);
    //@ pk_release_context_with_key(&context);
    pk_free(&context);
    //@ open pk_context(&context);
    //@ close [f]world(pub, key_clsfy);
    debug_print("signed item\n");
    print_buffer(output, (int) olen);

    // Create item
    if (olen < MINIMAL_STRING_SIZE)
      abort_crypto_lib("Assymetric signing failed: output to small");
    result->size = TAG_LENGTH + (int) olen;
    result->content = malloc((size_t)result->size);
    if (result->content == 0) {abort_crypto_lib("Malloc failed");}
    write_tag(result->content, TAG_ASYMMETRIC_SIG);
    //@ assert result->content |-> ?cont &*& result->size |-> ?size;
    crypto_memcpy(result->content + TAG_LENGTH, output, olen);
    //@ item e = asymmetric_signature_item(principal, count, some(pay), ent);
    //@ close ic_cg(e)(sig_ccs, sig_cg);
    //@ close item(payload, pay, pub);
    zeroize(output, (int) olen);
    free(output);
    //@ close well_formed_item_ccs(e)(pay_ccs);
    //@ leak well_formed_item_ccs(e)(pay_ccs);
    //@ CLOSE_ITEM_CONSTRAINTS(cont, TAG_ASYMMETRIC_SIG, size, e)
    //@ close item(result, e, pub);
  }
  debug_print("SINGING RESULT:\n");
  print_item(result);

  return result;
}

void asymmetric_signature_verify(struct item *key, struct item *item,
                                 struct item *signature)
  /*@ requires [?f]world(?pub, ?key_clsfy) &*&
               item(item, ?i, pub) &*& item(key, ?k, pub) &*&
               item(signature, ?sig, pub) &*&
                 sig == asymmetric_signature_item(?principal1, ?count1,
                                                  ?pay1, ?ent) &*&
               k == public_key_item(?principal2, ?count2); @*/
  /*@ ensures  [f]world(pub, key_clsfy) &*&
               item(item, i, pub) &*& item(key, k, pub) &*&
               item(signature, sig, pub) &*&
               switch(pay1)
               {
                 case some(pay2):
                   return col || (principal1 == principal2 &&
                                  count1 == count2 && i == pay2);
                 case none:
                   return true == col;
               }; @*/
{
  debug_print("ASYM SIGNATURE CHECKING:\n");
  print_item(signature);
  check_is_asymmetric_signature(signature);

  {
    pk_context context;
    unsigned int olen;
    char* output;

    // Key
    //@ close pk_context(&context);
    //@ open [f]world(pub, key_clsfy);
    pk_init(&context);
    //@ close [f]world(pub, key_clsfy);
    set_public_key(&context, key);
    /*@ assert pk_context_with_key(&context, pk_public,
                                   ?principal3, ?count3, RSA_BIT_KEY_SIZE); @*/
    // Signature checking
    //@ open item(item, ?i_old, pub);
    //@ assert item->content |-> ?i_cont &*& item->size |-> ?i_size;
    //@ assert crypto_chars(secret, i_cont, i_size, ?i_ccs);
    //@ assert [_]item_constraints(i, i_ccs, pub);
    //@ open item(signature, _, pub);
    //@ assert signature->content |-> ?s_cont &*& signature->size |-> ?s_size;
    //@ assert crypto_chars(secret, s_cont, s_size, ?sig_ccs);
    //@ OPEN_ITEM_CONSTRAINTS(sig, sig_ccs, pub)
    //@ assert [_]ic_parts(sig)(?sig_tag, ?sig_cont);
    //@ open [_]ic_cg(sig)(_, ?cg_sig);
    //@ assert cg_sig == cg_rsa_signature(principal1, count1, ?ccs_pay, ent);

    if (item->size > RSA_KEY_SIZE)
      abort_crypto_lib("Assymetric signature checking failed: incorrect sizes");

    //@ crypto_chars_limits(s_cont);
    //@ crypto_chars_split(s_cont, TAG_LENGTH);
    //@ assert crypto_chars(secret, s_cont, TAG_LENGTH, sig_tag);
    //@ assert crypto_chars(secret, s_cont + TAG_LENGTH, ?s, sig_cont);
    //@ assert s == s_size - TAG_LENGTH;
    //@ if (col) cg_sig = ccs_for_cg_sur(sig_cont, tag_asym_signature);
    //@ if (col) public_ccs_cg(cg_sig);
    //@ close cryptogram(s_cont + TAG_LENGTH, s, sig_cont, cg_sig);
    if(pk_verify(&context, MBEDTLS_MD_NONE, item->content,
                 (unsigned int) item->size,
                 signature->content + TAG_LENGTH,
                 (unsigned int) (signature->size - TAG_LENGTH)) != 0)
      abort_crypto_lib("Signing check failed: signature"
                       "was not created with the provided key");
    //@ pk_release_context_with_key(&context);
    pk_free(&context);

    //@ open pk_context(&context);
    //@ open cryptogram(s_cont + TAG_LENGTH, s, sig_cont, cg_sig);
    //@ crypto_chars_join(s_cont);
    //@ close item(signature, sig, pub);

    /*@ if (!col)
        {
          assert principal2 == principal3;
          assert count2 == count3;
          assert ccs_pay == i_ccs;
          open [_]item_constraints(i, ccs_pay, pub);
          switch(pay1)
          {
            case some(pay2):
              assert [_]item_constraints(pay2, ccs_pay, pub);
              item_constraints_injective(i, pay2, ccs_pay);
            case none:
              open [_]ill_formed_item_ccs(sig)(ccs_pay);
              assert false;
          }
        }
    @*/
    //@ close item(item, i, pub);
  }
}
