#include "asymmetric_signature_item.h"

#include "item_constraints.h"
#include "key_item.h"
#include "principals.h"
#include "serialization.h"
#include "deserialization.h"

#include <string.h>

bool is_asymmetric_signature(struct item *item)
  //@ requires item(item, ?i, ?pub);
  /*@ ensures  item(item, i, pub) &*&
               result ? i == asymmetric_signature_item(_, _, _, _) : true; @*/
{
  //@ open item(item, i, pub);
  //@ assert item->content |-> ?cont;
  //@ open chars(cont, ?size, ?cs);
  //@ open item_constraints(?b, i, cs, pub);
  //@ if (!b) open [_]item_constraints_no_collision(i, cs, pub);
  return *(item->content) == 'k';
  //@ close chars(cont, size, cs);
  //@ close item(item, i, pub);
}

void check_is_asymmetric_signature(struct item *item)
  //@ requires item(item, ?i, ?pub);
  /*@ ensures  item(item, i, pub) &*& 
               i == asymmetric_signature_item(_, _, _, _); @*/
{
  if (!is_asymmetric_signature(item))
    abort_crypto_lib("Presented item is not an asymmetric signature item");
}

/*@
lemma void info_for_asymmetric_signature_item(item key, item sig)
  requires [_]info_for_item(key, ?info1) &*&
           key == private_key_item(?p, ?c) &*&
           [_]info_for_item(sig, ?info2) &*&
           sig == asymmetric_signature_item(p, c, _, _);
  ensures  info1 == info2;
{
  open [_]info_for_item(key, info1);
  open [_]info_for_item(sig, info2);
}
@*/

int asym_sig_havege_random_stub(void *havege_state, char *output, size_t len)
  /*@ requires [?f]havege_state_initialized(havege_state) &*&
               random_request(?principal, ?info, ?key_request) &*&
               polarssl_generated_values(principal, ?count) &*&
               chars(output, len, _) &*& len >= POLARSSL_MIN_RANDOM_BYTE_SIZE;
  @*/
  /*@ ensures  [f]havege_state_initialized(havege_state) &*&
               polarssl_generated_values(principal, count + 1) &*&
               result == 0 ?
                 polarssl_cryptogram(output, len, ?cs, ?cg) &*&
                 info == polarssl_cryptogram_info(cg) &*&
                 key_request ?
                   cg == polarssl_symmetric_key(principal, count + 1)
                 :
                   cg == polarssl_random(principal, count + 1)
               :
                 chars(output, len, _);
  @*/
{
  return havege_random(havege_state, output, len);
}

struct item *asymmetric_signature(struct item *key, struct item *payload)
  /*@ requires [?f]world(?pub) &*&
               generated_values(?principal1, ?count1) &*&
               item(payload, ?pay, pub) &*& item(key, ?k, pub) &*& 
               k == private_key_item(?principal2, ?count2); @*/
  /*@ ensures  [f]world(pub) &*&
               generated_values(principal1, count1 + 1) &*&
               item(payload, pay, pub) &*& item(key, k, pub) &*& 
               item(result, ?sig, pub) &*& 
               collision_in_run() ?
                 true
               :
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
    unsigned int olen;
    char* output;
    
    //@ close pk_context(&context);
    //@ open [f]world(pub);
    pk_init(&context);
    set_private_key(&context, key);
    /*@ assert pk_context_with_key(&context, pk_private, 
                                   RSA_BIT_KEY_SIZE, ?id_key); @*/
    /*@ assert collision_in_run() ? 
                            true : id_key == some(pair(principal2, count2)); @*/
    
    // Signing
    //@ open item(payload, pay, pub);
    //@ assert payload->content |-> ?pay_cont &*& payload->size |-> ?pay_size;
    //@ assert chars(pay_cont, pay_size, ?pay_cs);
    //@ assert [_]item_constraints(_, pay, pay_cs, pub);
    if (payload->size < POLARSSL_MIN_HMAC_INPUT_BYTE_SIZE ||
        payload->size > RSA_KEY_SIZE) 
      abort_crypto_lib("Assymetric signing failed: incorrect sizes");
    output = malloc(RSA_KEY_SIZE);
    if (output == 0) abort_crypto_lib("Malloc failed");
      
    void *random_state = nonces_expose_state();
    //@ close random_function_predicate(havege_state_initialized);
    /*@ produce_function_pointer_chunk random_function(
                      asym_sig_havege_random_stub)
                     (havege_state_initialized)(state, out, len) { call(); } @*/
    //@ open generated_values(principal1, count1);
    
    if(pk_sign(&context, POLARSSL_MD_NONE,
               payload->content, (unsigned int) payload->size,
               output, &olen,
               asym_sig_havege_random_stub, random_state) != 0)
      abort_crypto_lib("Signing failed");    
    //@ close generated_values(principal1, count1 + 1);
    //@ polarssl_cryptogram sig_cg;
    /*@ switch(id_key)
        {
          case some(pair) :
            switch (pair)
            { 
              case pair(principal2', count2'):
                open polarssl_cryptogram(output, _, _, ?sig_cg2);
                assert sig_cg2 == polarssl_asym_signature(principal2', count2', 
                                                          pay_cs, ?ent);
                if (principal2 == principal2' && count2 == count2')
                  sig_cg = sig_cg2;
                else
                  assert true == collision_in_run();
            };
          case none:
            assert true == collision_in_run();
        }
    @*/
    //@ assert chars(output, ?sig_length, ?sig_cs);
    //@ assert u_integer(&olen, sig_length);
    //@ assert sig_length > 0 &*& sig_length <= RSA_KEY_SIZE;
    nonces_hide_state(random_state);
    //@ pk_release_context_with_key(&context);
    pk_free(&context);
    //@ open pk_context(&context);
    //@ close [f]world(pub);

    debug_print("signed item\n");
    print_buffer(output, (int) olen);
    
    // Create item
    result->size = 1 + (int) olen;
    result->content = malloc(result->size);
    if (result->content == 0) {abort_crypto_lib("Malloc failed");} 
    *(result->content) = 'k';
    //@ assert result->content |-> ?cont &*& result->size |-> ?size;
    memcpy(result->content + 1, output, olen);
    //@ assert chars(cont, size, ?cs);
    /*@ if (collision_in_run())
        {
          item e = dummy_item_for_tag('k');
          collision_public(pub, cs);
          polarssl_cryptograms_in_chars_upper_bound_from(cs, 
                      polarssl_generated_public_cryptograms(polarssl_pub(pub)));
          close item_constraints(true, e, cs, pub);
          leak item_constraints(true, e, cs, pub);
          close item(result, e, pub);
        }
        else
        {
          assert sig_cg == polarssl_asym_signature(principal2, count2,
                                                   pay_cs, ?ent);
          item e = asymmetric_signature_item(principal2, count2, 
                                             some(pay), ent);
          item_constraints_well_formed(pay, e);
          open [_]item_constraints(_, pay, pay_cs, pub);
          open [_]item_constraints_no_collision(pay, pay_cs, pub);
          close item_constraints_no_collision(e, cs, pub);
          leak item_constraints_no_collision( e, cs, pub);
          close item_constraints(false, e, cs, pub);
          leak item_constraints(false, e, cs, pub);
          close item(result, e, pub);
        }
    @*/
    //@ close item(payload, pay, pub);
    //@ chars_join(output);
    free(output);
  }
  
  debug_print("SINGING RESULT:\n");
  print_item(result);

  return result;
}

void asymmetric_signature_verify(struct item *key, struct item *item, 
                                 struct item *signature)
  /*@ requires [?f]world(?pub) &*&
               item(item, ?i, pub) &*& item(key, ?k, pub) &*&
               item(signature, ?sig, pub) &*&
               k == public_key_item(?principal1, ?count1); @*/
  /*@ ensures  [f]world(pub) &*&
               item(item, i, pub) &*& item(key, k, pub) &*& 
               item(signature, sig, pub) &*& 
               collision_in_run() ? 
                 true
               :
                 sig == asymmetric_signature_item(principal1, count1, 
                                                  some(i), _); @*/
{
  debug_print("ASYM SIGNATURE CHECKING:\n");
  print_item(signature);
  check_is_asymmetric_signature(signature);
  //@ assert sig == asymmetric_signature_item(?principal2, ?count2, ?pay2, ?ent2);
  
  {
    pk_context context;
    unsigned int olen;
    char* output;
    
    //@ close pk_context(&context);
    //@ open [f]world(pub);
    pk_init(&context);
    set_public_key(&context, key);
    /*@ assert pk_context_with_key(&context, pk_public, 
                                   RSA_BIT_KEY_SIZE, ?id_key); @*/
    /*@ assert collision_in_run() ? 
                            true : id_key == some(pair(principal1, count1)); @*/
    
    // Signature checking
    //@ open item(item, i, pub);
    //@ assert item->content |-> ?i_cont &*& item->size |-> ?i_size;
    //@ assert chars(i_cont, i_size, ?i_cs);
    //@ open [_]item_constraints(_, i, i_cs, pub);
    if (item->size < POLARSSL_MIN_HMAC_INPUT_BYTE_SIZE ||
        item->size > RSA_KEY_SIZE) 
      abort_crypto_lib("Assymetric signature checking failed: incorrect sizes");
    //@ open item(signature, sig, pub);
    //@ assert signature->content |-> ?sig_cont &*& signature->size |-> ?sig_size;
    //@ chars_limits(signature->content);
    //@ open chars(sig_cont, sig_size, _);
    //@ assert chars(sig_cont + 1, sig_size - 1, ?sig_cs);
    if(pk_verify(&context, POLARSSL_MD_NONE, item->content, 
                 (unsigned int) item->size,
                 signature->content + 1, 
                 (unsigned int) (signature->size - 1)) != 0)
      abort_crypto_lib("Signing check failed: signature"
                       "was not created with the provided key");
    //@ pk_release_context_with_key(&context);
    pk_free(&context);
    //@ open pk_context(&context);
    //@ close [f]world(pub);

    /*@ if (!collision_in_run())
        {
          switch(id_key)
          {
            case some(pair) :
              switch (pair)
              { 
                case pair(principal1', count1'):
                  if (principal1 == principal1' && count1 == count1')
                  {
                    assert exists<list<char> >(?ent);
                    polarssl_cryptogram cg1 = polarssl_asym_signature(
                                                 principal1, count1, i_cs, ent);
                    sig_cs == polarssl_chars_for_cryptogram(cg1);
                    open [_]item_constraints(_, sig, _, pub);
                    open [_]item_constraints_no_collision(sig, _, pub);
                    switch (pay2)
                    {
                      case some(pay):
                        assert [_]well_formed_item_chars(sig)(?cs_pay0);
                        polarssl_cryptogram cg2 = 
                                      polarssl_asym_signature(
                                             principal2, count2, cs_pay0, ent2);
                        assert sig_cs == polarssl_chars_for_cryptogram(cg2);
                        polarssl_chars_for_cryptogram_injective(cg1, cg2);
                        assert cs_pay0 == i_cs;
                        item_constraints_no_collision_injective(i_cs, i, pay);
                      case none:
                        open [_]ill_formed_item_chars(sig)(?cs_pay0);
                        polarssl_cryptogram cg2 = 
                                       polarssl_asym_signature(
                                             principal2, count2, cs_pay0, ent2);
                        assert sig_cs == polarssl_chars_for_cryptogram(cg2);
                        polarssl_chars_for_cryptogram_injective(cg1, cg2);
                        assert cs_pay0 == i_cs;
                        open [_]well_formed_item_chars(i)(i_cs);
                        assert false;
                    }
                  }
                  else
                  {
                    assert false;
                  }
              };
            case none:
              assert false;
          }
        }
    @*/
    
    //@ close item(item, i, pub);
    //@ close item(signature, sig, pub);
  }
}
