#include "asymmetric_encrypted_item.h"

#include "item_constraints.h"
#include "key_item.h"
#include "principals.h"
#include "serialization.h"
#include "deserialization.h"

#include <string.h>

bool is_asymmetric_encrypted(struct item *item)
  //@ requires item(item, ?i, ?pub);
  /*@ ensures  item(item, i, pub) &*&
               result ? i == asymmetric_encrypted_item(_, _, _, _) : true; @*/
{
  //@ open item(item, i, pub);
  //@ assert item->content |-> ?cont;
  //@ open chars(cont, ?size, ?cs);
  //@ open item_constraints(?b, i, cs, pub);
  //@ if (!b) open [_]item_constraints_no_collision(i, cs, pub);
  return *(item->content) == 'j';
  //@ close chars(cont, size, cs);
  //@ close item(item, i, pub);
}

void check_is_asymmetric_encrypted(struct item *item)
  //@ requires item(item, ?i, ?pub);
  /*@ ensures  item(item, i, pub) &*& 
               i == asymmetric_encrypted_item(_, _, _, _); @*/
{
  if (!is_asymmetric_encrypted(item))
    abort_crypto_lib("Presented item is not an asymmetric encrypted item");
}

/*@
lemma void info_for_asymmetric_encrypted_item(item key, item enc)
  requires [_]info_for_item(key, ?info1) &*&
           key == public_key_item(?p, ?c) &*&
           [_]info_for_item(enc, ?info2) &*&
           enc == asymmetric_encrypted_item(p, c, _, _);
  ensures  info1 == info2;
{
  open [_]info_for_item(key, info1);
  open [_]info_for_item(enc, info2);
}
@*/

int asym_enc_havege_random_stub(void *havege_state, char *output, size_t len)
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

struct item *asymmetric_encryption(struct item *key, struct item *payload)
  /*@ requires [?f]world(?pub) &*&
               generated_values(?principal1, ?count1) &*&
               item(payload, ?pay, pub) &*& item(key, ?k, pub) &*& 
               k == public_key_item(?principal2, ?count2); @*/
  /*@ ensures  [f]world(pub) &*&
               generated_values(principal1, count1 + 1) &*&
               item(payload, pay, pub) &*& item(key, k, pub) &*& 
               item(result, ?enc, pub) &*& 
               collision_in_run() ?
                 true
               :
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
    
    //@ close pk_context(&context);
    //@ open [f]world(pub);
    pk_init(&context);
    set_public_key(&context, key);
    /*@ assert pk_context_with_key(&context, pk_public, 
                                   RSA_BIT_KEY_SIZE, ?id_key); @*/
    /*@ assert collision_in_run() ? 
                            true : id_key == some(pair(principal2, count2)); @*/
    
    // Encryption
    //@ open item(payload, pay, pub);
    //@ assert [_]item_constraints(_, pay, ?pay_cs, pub);
    if (payload->size < POLARSSL_MIN_ENCRYPTED_BYTE_SIZE ||
        payload->size > RSA_KEY_SIZE) 
      abort_crypto_lib("Assymetric encryption failed: incorrect sizes");
      
    void *random_state = nonces_expose_state();
    //@ close random_function_predicate(havege_state_initialized);
    /*@ produce_function_pointer_chunk random_function(
                      asym_enc_havege_random_stub)
                     (havege_state_initialized)(state, out, len) { call(); } @*/
    //@ open generated_values(principal1, count1);
    if(pk_encrypt(&context, payload->content, (unsigned int) payload->size, 
                  output, &olen, MAX_PACKAGE_SIZE,
                  asym_enc_havege_random_stub, random_state) != 0)
      abort_crypto_lib("Encryption failed");
    //@ close generated_values(principal1, count1 + 1);
    //@ polarssl_cryptogram enc_cg;
    /*@ switch(id_key)
        {
          case some(pair) :
            switch (pair)
            { 
              case pair(principal2', count2'):
                open polarssl_cryptogram(output, _, _, ?enc_cg2);
                assert enc_cg2 == polarssl_asym_encrypted(principal2', count2', 
                                                          pay_cs, ?ent);
                if (principal2 == principal2' && count2 == count2')
                  enc_cg = enc_cg2;
                else
                  assert true == collision_in_run();
            };
          case none:
            assert true == collision_in_run();
        }
    @*/
    //@ assert chars(output, ?enc_length, ?enc_cs);
    //@ assert u_integer(&olen, enc_length);
    //@ assert enc_length > 0 &*& enc_length < MAX_PACKAGE_SIZE;
    //@ assert enc_length > 0 &*& enc_length <= RSA_SERIALIZED_KEY_SIZE;
    nonces_hide_state(random_state);
    //@ pk_release_context_with_key(&context);
    pk_free(&context);
    //@ open pk_context(&context);
    //@ close [f]world(pub);
    
    // Create item
    result->size = 1 + (int) olen;
    result->content = malloc(result->size);
    if (result->content == 0) {abort_crypto_lib("Malloc failed");} 
    *(result->content) = 'j';
    //@ assert result->content |-> ?cont &*& result->size |-> ?size;
    memcpy(result->content + 1, output, olen);
    //@ assert chars(cont, size, ?cs);
    /*@ if (collision_in_run())
        {
          item e = dummy_item_for_tag('j');
          collision_public(pub, cs);
          polarssl_cryptograms_in_chars_upper_bound_from(cs, 
                      polarssl_generated_public_cryptograms(polarssl_pub(pub)));
          close item_constraints(true, e, cs, pub);
          leak item_constraints(true, e, cs, pub);
          close item(result, e, pub);
        }
        else
        {
          assert enc_cg == polarssl_asym_encrypted(principal2, count2,
                                                   pay_cs, ?ent);
          item e = asymmetric_encrypted_item(principal2, count2, 
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
  }
  
  debug_print("ENCRYPTING RESULT:\n");
  print_item(result);

  return result;
}

struct item *asymmetric_decryption(struct item *key, struct item *item)
  /*@ requires [?f]world(?pub) &*&
               generated_values(?principal1, ?count1) &*&
               item(item, ?enc, pub) &*& item(key, ?k, pub) &*&
               enc == 
                 asymmetric_encrypted_item(?principal2, ?count2, ?pay, ?ent) &*&
               k == private_key_item(?principal3, ?count3); @*/
  /*@ ensures  [f]world(pub) &*&
               generated_values(principal1, count1 + 1) &*&
               item(item, enc, pub) &*& item(key, k, pub) &*& 
               item(result, ?dec, pub) &*& 
               collision_in_run() ? true :
               ( 
                 count2 == count3 && principal2 == principal3 ?
                   pay == some(dec)
                 :
                   [_]pub(dec)
               ); @*/
{
  debug_print("DECRYPTING:\n");
  print_item(item);

  struct item* result;
  result = malloc(sizeof(struct item));
  if (result == 0) abort_crypto_lib("Malloc failed");
  
  {
    pk_context context;
    unsigned int olen;
    char output[MAX_PACKAGE_SIZE];
    
    //@ close pk_context(&context);
    //@ open [f]world(pub);
    pk_init(&context);
    set_private_key(&context, key);
    /*@ assert pk_context_with_key(&context, pk_private, 
                                   RSA_BIT_KEY_SIZE, ?id_key); @*/
    /*@ assert collision_in_run() ? 
                            true : id_key == some(pair(principal3, count3)); @*/
    
    // Decryption
    //@ open item(item, enc, pub);
    //@ open [_]item_constraints(_, enc, ?enc_cs, pub);
    if (item->size - 1 < POLARSSL_MIN_ENCRYPTED_BYTE_SIZE ||
        item->size - 1 > RSA_KEY_SIZE) 
      abort_crypto_lib("Assymetric decryption failed: incorrect sizes");
    //@ assert item->content |-> ?i_cont &*& item->size |-> ?i_size;
    //@ chars_limits(i_cont);
    //@ assert chars(i_cont + 1, i_size - 1, ?cg_cs);
    
    void *random_state = nonces_expose_state();
    //@ close random_function_predicate(havege_state_initialized);
    /*@ produce_function_pointer_chunk random_function(
                      asym_enc_havege_random_stub)
                     (havege_state_initialized)(state, out, len) { call(); } @*/
    //@ open generated_values(principal1, count1);
    if(pk_decrypt(&context, item->content + 1, (unsigned int) item->size - 1, 
                  output, &olen, MAX_PACKAGE_SIZE,
                  asym_enc_havege_random_stub, random_state) != 0)
      abort_crypto_lib("Decryption failed");
    //@ close generated_values(principal1, count1 + 1);
    //@ assert u_integer(&olen, ?size_out);
    //@ assert chars(output, size_out, ?cs_out);
    parse_item(output, (int) olen);
    nonces_hide_state(random_state);
    //@ pk_release_context_with_key(&context);
    pk_free(&context);
    //@ open pk_context(&context);
    //@ close [f]world(pub);
    //@ assert exists<polarssl_cryptogram>(?cg_enc);
    /*@ assert cg_enc == polarssl_asym_encrypted(?principal4, ?count4, 
                                                 ?cs_out4, ?ent4); @*/
    
    result->size = (int) olen;
    result->content = malloc(result->size);
    if (result->content == 0) {abort_crypto_lib("Malloc failed");}
    memcpy(result->content, output, olen);
    //@ assert result->content |-> ?cont;
    //@ assert chars(cont, size_out, cs_out);
    
    /*@ if (collision_in_run())
        {
          item e = dummy_item_for_tag(head(cs_out));
          well_formed_valid_tag(cs_out, nat_length(cs_out));
          tag_for_dummy_item(e, head(cs_out));
          collision_public(pub, cs_out);
          polarssl_cryptograms_in_chars_upper_bound_from(cs_out, 
                      polarssl_generated_public_cryptograms(polarssl_pub(pub)));
          close item_constraints(true, e, cs_out, pub);
          leak item_constraints(true, e, cs_out, pub);
          close item(result, e, pub);
        }
        else
        {
          open [_]item_constraints_no_collision(enc, enc_cs, pub);
          assert enc_cs == cons('j', cg_cs);
          switch(pay)
          {
            case some(pay1):
              assert [_]well_formed_item_chars(enc)(?cs_pay0);
              polarssl_cryptogram cg_enc2 = 
                                   polarssl_asym_encrypted(
                                              principal2, count2, cs_pay0, ent);
              polarssl_chars_for_cryptogram_injective(cg_enc, cg_enc2);
            case none:
              open [_]ill_formed_item_chars(enc)(?cs_pay0);
              polarssl_cryptogram cg_enc2 = 
                                   polarssl_asym_encrypted(
                                              principal2, count2, cs_pay0, ent);
              polarssl_chars_for_cryptogram_injective(cg_enc, cg_enc2);
          }
          assert principal4 == principal2;
          assert count4 == count2;
          if (principal4 == principal3 && count4 == count3)
          {
            switch(pay)
            {
              case some(pay1):
                assert [_]well_formed_item_chars(enc)(?cs_pay0);
                assert [_]item_constraints_no_collision(pay1, cs_pay0, pub);
                close item_constraints(false, pay1, cs_pay0, pub);
                leak item_constraints(false, pay1, cs_pay0, pub);
                close item(result, pay1, pub);
              case none:
                open [_]ill_formed_item_chars(enc)(?cs_pay0);
                polarssl_generated_public_cryptograms_subset( 
                                                    polarssl_pub(pub), cs_pay0);
                deserialize_item(cs_pay0, pub);
                leak proof_obligations(pub);
                assert [_]item_constraints_no_collision(?pay1, cs_pay0, pub); 
                item_constraints_no_collision_well_formed(pay1, pay1);
                open  [_]well_formed_item_chars(pay1)(cs);
                assert false;
            }
          }
          else
          {
            assert nil == polarssl_cryptograms_in_chars(cs_out);
            retreive_proof_obligations();
            polarssl_generated_public_cryptograms_subset(
                                              polarssl_pub(pub), cs_out);
            deserialize_item(cs_out, pub);
            leak proof_obligations(pub);
            assert [_]item_constraints_no_collision(?i, cs_out, pub);
            close item_constraints(false, i, cs_out, pub);
            leak item_constraints(false, i, cs_out, pub);
            close item(result, i, pub);
          }
        }
    @*/
    //@ close item(item, enc, pub);
  }
    
  debug_print("DECRYPTING RESULT:\n");
  print_item(result);
  
  return result;
}

