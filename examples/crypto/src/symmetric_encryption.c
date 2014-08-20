#include "symmetric_encryption.h"

#include "item.h"
#include "key_item.h"
#include "principals.h"
#include "encrypted_item.h"

void check_valid_symmetric_encrypted_item_chars_size(int cs_size)
  //@ requires true;
  //@ ensures  cs_size > sizeof(char) + sizeof(int) + AES_IV_SIZE;
{
  if (cs_size <= (int) sizeof(char) + (int) sizeof(int)+ AES_IV_SIZE)
    abort_crypto_lib("Illegal size for encrypted item");
}

struct item *sym_encrypt(struct item *key, struct item *payload)
  /*@ requires [?f]world(?pub) &*&
               item(key, ?key_i) &*& 
               key_i == key_item(?s, ?count1, symmetric_key, ?info) &*&
               item(payload, ?pay_i) &*&
               generated_values(?principal, ?count2);
  @*/
  /*@ ensures  [f]world(pub) &*&
               item(key, key_item(s, count1, symmetric_key, info)) &*&
               item(payload, pay_i) &*&
               generated_values(principal, count2 + 1) &*&
               item(result, encrypted_item(?key_enc, ?pay_enc, ?entropy)) &*&
               true == if_no_collision(key_enc == key_i && pay_enc == pay_i);
  @*/
{
  debug_print("ENCRYPTING:\n");
  print_item(payload);

  struct item* result;
  
  {
    char* temp;
    
    int key_size;
    char *key_value;
    aes_context aes;

    char iv[AES_IV_SIZE];
    int iv_offset_i;
    size_t iv_offset = 0;
   
    char* input;
    int input_size;
    int output_size;
    char *buffer;  
    
    // Key stuff
    check_is_key(key);
    key_size = item_serialize(&temp, key);
    check_valid_symmetric_key_item_size(key_size);
    key_value = temp;
    //@ assert chars(key_value, key_size, ?key_cs);
    
    //@ close aes_context(&aes);
    //@ open [f]world(pub);
    if (aes_setkey_enc(&aes, key_value, (unsigned int) key_size) != 0)
      abort_crypto_lib("Invalid key provided for symmetric encryption");
    //@ assert aes_context_initialized(&aes, key_cs);
    //@ close [f]world(pub);

    // IV stuff
    random_buffer(iv, AES_IV_SIZE);
    //@ assert chars(iv, AES_IV_SIZE, ?iv_cs);
    
    // Entropy stuff
    char* entropy = malloc_wrapper(AES_IV_SIZE + (int) sizeof(int));
    buffer = entropy;
    iv_offset_i = (int) iv_offset;
    //@ assert integer(&iv_offset_i, ?iv_off_val);
    memcpy(buffer, &iv_offset_i, sizeof(int));
    buffer += (int) sizeof(int);
    memcpy(buffer, iv, AES_IV_SIZE);
    //@ list<char> ent_cs = append(chars_of_int(iv_off_val), iv_cs);
    
    //@ take_append(sizeof(int), chars_of_int(iv_off_val), iv_cs); 
    //@ drop_append(sizeof(int), chars_of_int(iv_off_val), iv_cs); 

    //@ assert u_integer(&iv_offset, ?iv_off_val_u);
    //@ assert (iv_cs == drop(sizeof(int), ent_cs ));
    /*@ assert (iv_off_val_u ==
                        int_of_chars(take(sizeof(int), ent_cs ))); @*/

    // Payload stuff;
    input_size = item_serialize(&temp, payload);
    input = temp;
    //@ assert chars(input, input_size, ?pay_cs);
    if (input_size > INT_MAX - (int) sizeof(char) 
                             - 3 * (int) sizeof(int) - AES_IV_SIZE)
      abort_crypto_lib("Message to encrypt was to big");
    output_size = (int) sizeof(char) + (int) sizeof(int) 
                  + AES_IV_SIZE + input_size;
    /*@ if (!collision_in_run())
        {
          assert key_cs == extended_chars_for_item(key_i);
          assert pay_cs == extended_chars_for_item(pay_i); 
          assert true == serialization_constraints(pay_i, pay_cs);
        }
    @*/
     
    // Encryption
    char *encrypted = malloc_wrapper(input_size);
    debug_print("input to encryption:\n");
    print_buffer(input, input_size);
    //@ open [f]world(pub);
    if (aes_crypt_cfb128(&aes, AES_ENCRYPT, (unsigned int) input_size, 
                         &iv_offset, iv, input, encrypted) != 0)
      abort_crypto_lib("Encryption failed");
    //@ aes_polarssl_item_to_chars(encrypted);
    //@ assert chars(encrypted, input_size, ?cs_enc);
    
    /*@ polarssl_item result_pi = 
            polarssl_aes_encrypted_item(extended_chars_for_item(key_i),
                                        iv_off_val_u, iv_cs, 
                                        extended_chars_for_item(pay_i)); @*/
    /*@ if (!collision_in_run())
        {
          assert cs_enc == aes_chars_for_polarssl_item(result_pi);
        }
    @*/   
    //@ aes_release_context(&aes);
    //@ open aes_context(&aes);
    //@ close [f]world(pub);
    debug_print("output of encryption:\n");
    print_buffer(encrypted, input_size);
    
    // Create item
    result = malloc(sizeof(struct item));
    if (result == 0)
      abort_crypto_lib("Malloc failed");
    result->tag = 5;
    result->size = output_size;
    result->content = malloc_wrapper(output_size);
    
    // Fill char buffer for this encrypted item
    *(result->content) = 'a';
    buffer = result->content + (int) sizeof(char);
    memcpy(buffer, entropy, (unsigned int) (AES_IV_SIZE + (int) sizeof(int)));
    
    //@ assert chars(buffer, AES_IV_SIZE + sizeof(int), ?cs_t1);
    //@ assert cs_t1 == ent_cs ;
    
    buffer += AES_IV_SIZE + (int) sizeof(int);
    memcpy(buffer, encrypted, (unsigned int) input_size);
    
    //@ assert chars(buffer, input_size, ?cs_t2);
    //@ assert cs_t2 == cs_enc;
    //@ assert result->content |-> ?cont; 
    //@ chars_join(cont + sizeof(char));
    //@ assert chars(cont, output_size, ?cs);
    /*@ assert chars(cont, 
                    sizeof(char) + sizeof(int) + AES_IV_SIZE + input_size, 
                    ?cs_t3); @*/
    //@ assert cs_t3 == cons('a', append(ent_cs, cs_enc));
    //@ item result_i = encrypted_item(key_i, pay_i, ent_cs);
                   
    //@ assert 5 == tag_for_item(result_i);
    //@ assert 0 < output_size && output_size <= INT_MAX - 2 * sizeof(int);
    
    //@ assert (cs == cons('a', append(ent_cs, cs_enc)));
    /*@ assert chars_for_item(result_i) == cons('a',
               append(
                ent_cs, aes_chars_for_polarssl_item(
                  polarssl_aes_encrypted_item(
                    extended_chars_for_item(key_i),
                    int_of_chars(take(sizeof(int), ent_cs)),
                    drop(sizeof(int), ent_cs),
                    extended_chars_for_item(pay_i)
                  )
                )
              )); @*/
    /*@ if (!collision_in_run())
        {
          assert cs_enc == aes_chars_for_polarssl_item(
                          polarssl_aes_encrypted_item(
                            extended_chars_for_item(key_i),
                            int_of_chars(take(sizeof(int), ent_cs)),
                            drop(sizeof(int), ent_cs), 
                            extended_chars_for_item(pay_i))
                        );
        }
    @*/
    /*@ equal_double_triple_append(
          chars_of_int(tag_for_item(key_i)),
          chars_of_int(length(chars_for_item(key_i))),
          chars_for_item(key_i),
          chars_of_int(tag_for_item(pay_i)),
          chars_of_int(length(chars_for_item(pay_i))),
          chars_for_item(pay_i)
        );
    @*/
    /*@
      if (!collision_in_run()) 
      {        
         close item(result, result_i);
      }
      else
      {
        close item(result, dummy_item_for_tag(5));
      }
    @*/
    
    // Cleanup
    free(key_value);
    free(input);
    free(entropy);
    free(encrypted);
  }
    
  debug_print("ENCRYPTING RESULT:\n");
  print_item(result);
  
  return result;
}

struct item *sym_decrypt(struct item *key, struct item *item)
  /*@ requires [?f]world(?pub) &*& item(item, ?i) &*&
               item(key, ?key_i) &*&
               key_i == key_item(?principal1, ?count1, symmetric_key, ?info);
  @*/
  /*@ ensures  [f]world(pub) &*& item(item, i) &*&
               item(key, key_i) &*&
               switch (i)
               {
                 case nonce_item(p0, c0, inc0, i0): return false;
                 case key_item(p0, c0, k0, i0): return false;
                 case data_item(d0): return false;
                 case hmac_item(k0, payload0): return false;
                 case encrypted_item(key0, pay0, ent0): return
                     item(result, ?result_i) &*&
                     true == if_no_collision(
                       key0 == key_item(principal1, count1, symmetric_key, info) &&
                       pay0 == result_i
                     );
                 case pair_item(f0, s0): return false;
               };
  @*/
{
  debug_print("DECRYPTING:\n");
  print_item(item);

  struct item* result;
  
  {
    char* temp;

    int key_size;
    char *key_value;
    aes_context aes;

    char iv[AES_IV_SIZE];
    int iv_offset_i;
    size_t iv_offset = 0;

    char* input;
    char* output1;
    char* output2;
    int input_size;
    char *buffer;

    // Key stuff
    check_is_key(key);
    key_size = item_serialize(&temp, key);
    check_valid_symmetric_key_item_size(key_size);
    key_value = temp;
    //@ assert chars(key_value, key_size, ?key_cs);
    
    //@ close aes_context(&aes);
    //@ open [f]world(pub);
    if (aes_setkey_enc(&aes, key_value, (unsigned int) key_size) != 0)
      abort_crypto_lib("Invalid key provided for symmetric encryption");
    //@ assert aes_context_initialized(&aes, key_cs);
    //@ close [f]world(pub);

    // Open encrypted item and retrieve data
    check_is_encrypted(item);
    //@ open item(item, ?enc_item);
    check_valid_symmetric_encrypted_item_chars_size(item->size);
    //@ assert enc_item == encrypted_item(?enc_key, ?enc_pay, ?enc_ent);

    //@ chars_limits(item->content);
    //@ chars_split(item->content, sizeof(char));
    //@ assert item->content |-> ?cont;
    //@ open chars(cont, 1, ?cs);
    if (*(item->content) != 'a')
      abort_crypto_lib("Wrong kind of key for decryption");
    
    //@ assert item->tag |-> ?enc_tag;
    //@ assert item->size |-> ?enc_size;
    //@ assert item->content |-> ?enc_cont;
    //@ assert chars(enc_cont, enc_size, ?enc_cs);
    /*@ if (!collision_in_run())
        {
          assert true == 
                     item_constraints(enc_item, enc_tag, enc_size, enc_cs);
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
              case symmetric_key:
                assert length(enc_ent) == AES_IV_SIZE + sizeof(int);
              case public_key: assert false;
              case private_key: assert false;
            }
          }
        }
    @*/

    buffer = item->content + (int) sizeof(char);
    char* entropy = malloc_wrapper(AES_IV_SIZE + (int) sizeof(int));
    memcpy(entropy, buffer, (unsigned int) (AES_IV_SIZE + (int) sizeof(int)));
    buffer += AES_IV_SIZE + (int) sizeof(int);
    input_size = item->size - (int) sizeof(char) - (int) sizeof(int) - AES_IV_SIZE;
    input = malloc_wrapper(input_size);
    memcpy(input, buffer, (unsigned int) input_size);
    /*@ polarssl_item pi1 = polarssl_aes_encrypted_item(
              extended_chars_for_item(enc_key),
              int_of_chars(take(sizeof(int), enc_ent)),
              drop(sizeof(int), enc_ent), 
              extended_chars_for_item(enc_pay)
            );
    @*/
    //@ assert chars(entropy, AES_IV_SIZE + (int) sizeof(int), ?entropy_cs);
    //@ assert chars(input, input_size, ?input_cs);
    //@ assert enc_cs == cons('a', append(entropy_cs, input_cs));
    /*@ if (!collision_in_run())
        {
          take_append(AES_IV_SIZE + sizeof(int), enc_ent,
                      aes_chars_for_polarssl_item(pi1));
          drop_append(AES_IV_SIZE + sizeof(int), enc_ent,
                      aes_chars_for_polarssl_item(pi1));
          assert entropy_cs == enc_ent;
          assert enc_cs == cons('a', append(enc_ent, aes_chars_for_polarssl_item(pi1)));
          assert input_cs == aes_chars_for_polarssl_item(pi1);
        }
    @*/

    // IV stuff
    buffer = entropy;
    memcpy(&iv_offset_i, buffer, sizeof(int));
    //@ chars_to_integer(&iv_offset_i);
    //@ assert integer(&iv_offset_i, ?iv_offset_i_val);
    /*@ if (!collision_in_run())
        {
          assert 0 <= int_of_chars(take(sizeof(int), enc_ent));
          assert 16 > int_of_chars(take(sizeof(int), enc_ent));
          assert 0 <= iv_offset_i_val;
          assert 16 > iv_offset_i_val;
        }
    @*/
    if (iv_offset_i < 0 || iv_offset_i >= 16) 
      {abort_crypto_lib("Found illegal IV offset during decryption");}
    iv_offset = (unsigned int) iv_offset_i;
    buffer += (int) sizeof(int);
    memcpy(iv, buffer, AES_IV_SIZE);
    //@ assert chars(iv, AES_IV_SIZE, ?cs_iv);
    /*@ if (!collision_in_run())
        {
          assert iv_offset == int_of_chars(take(sizeof(int), enc_ent));
          assert cs_iv == drop(sizeof(int), enc_ent);
        }
    @*/

    // Decryption
    char *decrypted = malloc_wrapper(input_size);
    debug_print("input to decryption:\n");
    print_buffer(input, input_size);
    //@ open [f]world(pub);
    //@ aes_chars_to_polarssl_item(input);
    //@ assert polarssl_item(input, ?pi2);
    //@ aes_chars_for_polarssl_item_injective(pi1, pi2);

        //@ assert collision_in_run() ? true : pi1 == pi2;
   
    if (aes_crypt_cfb128(&aes, AES_DECRYPT, (unsigned int) input_size, 
                         &iv_offset, iv, input, decrypted) != 0)
      abort_crypto_lib("Decryption failed");
    
    //@ aes_release_context(&aes);
    //@ open aes_context(&aes);
    //@ aes_polarssl_item_to_chars(input);
    //@ close [f]world(pub);
    debug_print("output of decryption:\n");
    print_buffer(decrypted, input_size);

    //Extracting decrypted content
    //@ assert chars(decrypted, input_size, ?dec_cs);
    //@ close deserialization_attempt(enc_pay, dec_cs);
    result = item_deserialize(decrypted, input_size);
    //@ assert item(result, ?result_i);
    
    /*@
      if (collision_in_run() == false)
      {
        if (
             key_cs == extended_chars_for_item(enc_key) &&
             iv_offset_i == int_of_chars(take(sizeof(int), enc_ent)) &&
             cs_iv == drop(sizeof(int), enc_ent)
           )
        {
          assert item(result, enc_pay);
          assert result_i == enc_pay;
          assert key_cs   == extended_chars_for_item(key_i);
          assert key_cs   == extended_chars_for_item(enc_key);
          open [f]world(pub);
          extended_chars_for_item_injective(key_i, enc_key);
          close [f]world(pub);
          assert key_i == enc_key;
        }
        else 
        {
          assert false;
        }
      }
      else
      {
        assert true;
      }
    @*/

    // Cleanup
    free(key_value);
    free(input);
    free(entropy);
    free(decrypted);
    //@ close item(item, encrypted_item(enc_key, enc_pay, enc_ent));
  }
  
  debug_print("DECRYPTING result:\n");
  print_item(result);
  
  return result;
}  
