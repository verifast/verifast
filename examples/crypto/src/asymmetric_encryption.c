#include "asymmetric_encryption.h"

#include "principals.h"
#include "item.h"
#include "encrypted_item.h"
#include "key_item.h"
#include "nonce_item.h"
#include "serialization.h"

int asym_encryption_havege_random_stub(void *havege_state, 
                                            char *output, size_t len)
  /*@ requires
        [?f0]polarssl_world<item>(?pub) &*&
        [?f1]havege_state_initialized(havege_state) &*&
        polarssl_generated_values(?principal, ?count) &*&
        havege_request(principal, ?info) &*&
        chars(output, len, _);
  @*/
  /*@ ensures
        [f0]polarssl_world<item>(pub) &*&
        [f1]havege_state_initialized(havege_state) &*&
        polarssl_generated_values(principal, count + 1) &*&
        polarssl_item(output, ?i) &*& 
        i == polarssl_havege_item(principal, count + 1) &*&
        len == length(havege_chars_for_polarssl_item(i)) &*&
        info == info_for_polarssl_item(i); @*/
{
  return havege_random(havege_state, output, len);
}

struct item *asym_encrypt(struct item *key, struct item *payload)
  /*@ requires [?f]world(?pub) &*&
               item(key, ?key_i) &*& 
               key_i == key_item(?principal1, ?count1, public_key, ?info) &*&
               item(payload, ?pay_i) &*&
               generated_values(?principal2, ?count2);
  @*/
  /*@ ensures  [f]world(pub) &*&
               item(key, key_item(principal1, count1, public_key, info)) &*&
               item(payload, pay_i) &*&
               generated_values(principal2, count2 + 1) &*&
               item(result, encrypted_item(?key_enc, ?pay_enc, ?entropy)) &*&
               true == if_no_collision(key_enc == key_i && pay_enc == pay_i);
  @*/
{
  char* temp;
  unsigned int olen;
  char output[MAX_PACKAGE_SIZE];
  
  // Key stuff
  check_is_key(key);
  int key_size = item_serialize(&temp, key);
  check_valid_asymmetric_key_item_size(key_size);
  free(temp);
  pk_context *context = malloc(sizeof(struct pk_context));
  if (context == 0) {abort_crypto_lib("Malloc failed");}  
  //@ close pk_context(context);
  //@ open [f]world(pub);
  pk_init(context);
  set_public_key(context, key);
  //@ close [f]world(pub);
  //@ assert pk_context_with_key(context, ?p_key, ?c_key, pk_public);
  /*@ if (!collision_in_run())
      {
        assert p_key == principal1;
        assert c_key == count1;
      }
  @*/
  
  // Payload stuff;
  int input_size = item_serialize(&temp, payload);
  //@ open [f]world(pub);
  //@ char* tempp = temp;
  //@ assert chars(tempp, input_size, ?cs_p);
  if (input_size > INT_MAX - (int) sizeof(char) - 2 * (int) sizeof(int))
      abort_crypto_lib("Message to encrypt was to big");
  /*@ if (!collision_in_run())
      {
        assert cs_p == extended_chars_for_item(pay_i); 
        assert true == serialization_constraints(pay_i, cs_p);
      }
  @*/

  // Encryption
  void *random_state = nonces_expose_state();
  /*@ produce_function_pointer_chunk random_function<item>(
           asym_encryption_havege_random_stub)()
           (state, out, len) { call(); } @*/
  //@ open generated_values(principal2, count2);
  if(pk_encrypt(context, temp, (unsigned int) input_size, output, &olen, MAX_PACKAGE_SIZE,
             asym_encryption_havege_random_stub, random_state) != 0)
    abort_crypto_lib("Encryption failed");
  //@ close generated_values(principal2, count2 + 1);
  //@ assert polarssl_item(output, polarssl_rsa_encrypted_item(?p_e, ?c_e, ?cs_e, ?ent));
  /*@ if (!collision_in_run())
      {
        assert p_e == principal1;
        assert c_e == count1;
        assert cs_e == cs_p;
      }
  @*/
  nonces_hide_state(random_state);
  
  // Create item
  struct item *result = malloc(sizeof(struct item));
  if (result == 0) {abort_crypto_lib("Malloc failed");}

  result->tag = 5;
  result->size = (int) olen + (int) sizeof(char);
  if(result->size <= 0 || result->size > INT_MAX - 2 * (int) sizeof(int))
    abort_crypto_lib("Encrypted item is to big");  
  result->content = malloc(result->size);
  if (result->content == 0) {abort_crypto_lib("Malloc failed");} 
  *(result->content) = 'b';
  //@ rsa_encrypted_polarssl_item_to_chars(output);
  //@ assert u_integer(&olen, ?olen_val);
  //@ assert chars((void*) output, olen_val, ?cs_pi);
  memcpy(result->content + (int) sizeof(char), output, olen);
  /*@
      if (!collision_in_run()) 
      {      
          assert (0 < length(chars_for_item(pay_i)));
          assert (length(chars_for_item(pay_i)) <= INT_MAX - 2 * sizeof(int));
          assert (true == item_constraints_recursive(pay_i));
          close item(result, encrypted_item(key_i, pay_i, ent));
       }
      else
      {
        close item(result, dummy_item_for_tag(5));
      }
  @*/
  
  // Cleanup
  free(temp);
  //@ pk_release_context_with_key(context);
  pk_free(context);
  //@ open pk_context(context);
  free(context);
  //@ close [f]world(pub);
  
  debug_print("item output of encryption:\n");
  print_item(result);
  
  return result;
}

struct item *asym_decrypt(struct item *key, struct item *item)
  /*@ requires [?f]world(?pub) &*& item(item, ?i) &*&
               item(key, ?key_i) &*&
               key_i == key_item(?principal1, ?count1, private_key, ?info) &*&
               generated_values(?principal2, ?count2);
  @*/
  /*@ ensures  [f]world(pub) &*& item(item, i) &*&
               item(key, key_i) &*&
               generated_values(principal2, count2 + 1) &*&
               switch (i)
               {
                 case nonce_item(p0, c0, inc0, i0): return false;
                 case key_item(p0, c0, k0, i0): return false;
                 case data_item(d0): return false;
                 case hmac_item(k0, payload0): return false;
                 case encrypted_item(key0, pay0, ent0): return
                     item(result, ?result_i) &*&
                     true == if_no_collision(
                       key0 == key_item(principal1, count1, public_key, info) && 
                       pay0 == result_i
                     );
                 case pair_item(f0, s0): return false;
               };
  @*/
{
  char* temp;
  unsigned int olen;
  char output[MAX_PACKAGE_SIZE];

  // Key stuff
  check_is_private_key(key);
  int key_size = item_serialize(&temp, key);
  check_valid_asymmetric_key_item_size(key_size);
  free(temp);
  pk_context *context = malloc(sizeof(struct pk_context));
  if (context == 0) {abort_crypto_lib("Malloc failed");}  
  //@ close pk_context(context);
  //@ open [f]world(pub);
  pk_init(context);
  set_private_key(context, key);
  //@ close [f]world(pub);
  //@ assert pk_context_with_key(context, ?p_key, ?c_key, pk_private);
  /*@ if (!collision_in_run())
      {
        assert p_key == principal1;
        assert c_key == count1;
      }
  @*/
  
  // Open encrypted item and retrieve data
  check_is_encrypted(item);
  //@ open item(item, ?enc_item);
  check_valid_encrypted_item_chars_size(item->size);
  //@ assert enc_item == encrypted_item(?enc_key, ?enc_pay, ?enc_ent);
  
  //@ chars_limits(item->content);
  //@ chars_split(item->content, sizeof(char));
  //@ assert item->content |-> ?cont;
  //@ open chars(cont, 1, ?cs);
  if (*(item->content) != 'b')
      abort_crypto_lib("Corrupted encrypted item");
  //@ assert item->tag |-> ?enc_tag;
  //@ assert item->size |-> ?enc_size;
  //@ assert item->content |-> ?enc_cont;
  //@ assert chars(enc_cont, enc_size, ?enc_cs);
  /*@ if (!collision_in_run())
      {
        assert true ==
                    item_constraints(enc_item, enc_tag, enc_size, enc_cs);
      }
  @*/
    
  int input_size = item->size - (int) sizeof(char);
  char *input = malloc(input_size);
  if (input == 0) {abort_crypto_lib("Malloc failed");}
  memcpy(input, item->content + (int) sizeof(char), (unsigned int) input_size);
  //@ assert chars(input, input_size, ?input_cs);
  //@ assert enc_cs == cons('b', input_cs);
  //@ open [f]world(pub);
  if (input_size > INT_MAX - (int) sizeof(char) - 2 * (int) sizeof(int))
      abort_crypto_lib("Message to encrypt was to big");
  //@ rsa_encrypted_chars_to_polarssl_item(input);
  //@ assert polarssl_item(input, ?pi1);
  //@ assert pi1 == polarssl_rsa_encrypted_item(?p_pi1, ?c_pi1, ?pay_pi1, ?e_pi1);
  //@ assert input_cs == rsa_encrypted_chars_for_polarssl_item(pi1);
  
  // Decryption
  void *random_state = nonces_expose_state();
  /*@ produce_function_pointer_chunk random_function<item>(
           asym_encryption_havege_random_stub)()
           (state, out, len) { call(); } @*/
  //@ open generated_values(principal2, count2);
  if(pk_decrypt(context, input, (unsigned int) input_size, output, &olen, MAX_PACKAGE_SIZE,
             asym_encryption_havege_random_stub, random_state) != 0)
    abort_crypto_lib("Decryption failed");
  //@ close generated_values(principal2, count2 + 1);
  
  //@ assert u_integer(&olen, ?olen_val);
  //@ u_integer_limits(&olen);
  //@ chars_limits(output);
  //@ assert chars(output, ?output_len, ?output_cs);
  /*@ if (!collision_in_run())
      {
        assert output_len == olen_val; 
        assert chars((void*) output + olen_val, MAX_PACKAGE_SIZE - olen_val, _);
        assert output_cs == pay_pi1;
      }
  @*/
  //@ rsa_encrypted_polarssl_item_to_chars(input);
  nonces_hide_state(random_state);
  if(olen > (unsigned int) INT_MAX ||
     (int) olen > MAX_PACKAGE_SIZE)
    abort_crypto_lib("Decryption failed");

  // Create item
  /*@ if (!collision_in_run())
      {
        close deserialization_attempt(enc_pay, output_cs);
        switch (enc_key)
        {
          case data_item(d0): assert false;
          case pair_item(f0, s0): assert false;
          case nonce_item(p0, c0, inc0, i0): assert false;
          case hmac_item(k0, pay0): assert false;
          case encrypted_item(k0, pay0, ent0): assert false;
          case key_item(p0, c0, k0, i0):
            switch(k0)
            {
              case symmetric_key: assert false;
              case public_key:
                polarssl_item pi2 = 
                            polarssl_rsa_encrypted_item(p0, c0, 
                              append(chars_of_int(tag_for_item(enc_pay)),
                                append(chars_of_int(length(chars_for_item(enc_pay))),
                                      chars_for_item(enc_pay))), enc_ent);
                assert enc_cs == cons('b', rsa_encrypted_chars_for_polarssl_item(pi2));
                rsa_encrypted_chars_for_polarssl_item_injective(pi1, pi2);
                assert pi1 == pi2;
                assert info_for_polarssl_item(pi1) == info_for_polarssl_item(pi2);
                assert i0 == info_for_polarssl_item(polarssl_rsa_public_key_item(p0, c0));
                assert chars(output, output_len, output_cs);
                assert output_cs == append(chars_of_int(tag_for_item(enc_pay)),
                                      append(chars_of_int(length(chars_for_item(enc_pay))),
                                        chars_for_item(enc_pay)));
                assert enc_key == key_item(p0, c0, public_key, i0);
                assert key_i == key_item(p0, c0, private_key, _);
                assert key_i == key_item(p0, c0, private_key, i0);
                assert true == serialization_constraints(enc_pay, output_cs);
              case private_key: assert false;
            }
        }
      }
      else
      {
        assert chars(output, olen_val, ?output_cs_temp);
        close deserialization_attempt(enc_pay, output_cs_temp);
      }
  @*/

  //@ close [f]world(pub);
  struct item *result = item_deserialize(output, (int) olen);
  //@ open [f]world(pub);
  
  // Cleanup
  free(input);
  //@ pk_release_context_with_key(context);
  pk_free(context);
  //@ open pk_context(context);
  free(context);
  //@ close [f]world(pub);
  //@ close item(item, enc_item);
  
  debug_print("item output of decryption:\n");
  print_item(result);
  
  return result;
}