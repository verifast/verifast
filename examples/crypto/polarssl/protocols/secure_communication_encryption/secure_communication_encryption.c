#include "secure_communication_encryption.h"

#include "../../src/random.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

//@ #include <listex.gh>
//@ #include <quantifiers.gh>

#define APP_RECEIVE_PORT 121212

void app_send(char *key, char *message, int message_len)
  /*@ requires [?f0]polarssl_world<unit>(sc_enc_polarssl_pub,
                                         sc_enc_polarssl_proof_pred, 
                                         unit) &*&
               [?f1]polarssl_cryptogram(key, KEY_BYTE_SIZE, ?key_cs, ?key_cg) &*&
                 key_cg == polarssl_symmetric_key(?creator, ?key_id) &*&
               [?f2]polarssl_public_message(sc_enc_polarssl_pub)
                                           (message, message_len, ?m_cs) &*&
                 message_len >= POLARSSL_MIN_ENCRYPTED_BYTE_SIZE &*&
                 message_len < POLARSSL_MAX_MESSAGE_BYTE_SIZE - 84 &*&
               polarssl_generated_values(creator, ?count1) &*&
               app_send_event(creator, m_cs) == true;
  @*/
  /*@ ensures  [f0]polarssl_world<unit>(sc_enc_polarssl_pub,
                                        sc_enc_polarssl_proof_pred, 
                                        unit) &*&
               [f1]polarssl_cryptogram(key, KEY_BYTE_SIZE, key_cs, key_cg) &*&
               [f2]polarssl_public_message(sc_enc_polarssl_pub)
                                          (message, message_len, m_cs) &*&
               polarssl_generated_values(creator, ?count2) &*&
               count2 > count1;
  @*/
{
  int socket;
  havege_state havege_state;
  int iv_off;
  char iv[16];
  char* encrypted = malloc(message_len);
  if (encrypted == 0) abort();
  
  // init
  {
    net_usleep(20000);
    if(net_connect(&socket, NULL, APP_RECEIVE_PORT) != 0)
      abort();
    if(net_set_block(socket) != 0)
      abort();
      
    //@ close havege_state(&havege_state);
    havege_init(&havege_state);
  }
  
  // iv stuff
  {
    r_int_with_bounds(&havege_state, &iv_off, 0, 15);
    //@ close random_request(creator, 0, false);
    if (havege_random(&havege_state, iv, 16) != 0) abort();  
  }
  //@ assert integer(&iv_off, ?iv_val) &*& iv_val >=0 &*& iv_val <= 15;
  //@ open polarssl_cryptogram(iv, 16, ?iv_cs, _);
  
  char* m = malloc(20 + message_len + 64);
  if (m == 0) abort();
  memcpy(m, (void*) &iv_off, 4);
  memcpy(m + 4, iv, 16);
  //@ chars_join(m);
  //@ assert chars(m, 20, ?cs1);
  //@ polarssl_generated_public_cryptograms_assume(sc_enc_polarssl_pub, cs1);
  
  // encrypt message
  {
    unsigned int temp;
    aes_context aes_context;
    //@ close aes_context(&aes_context);
    //@ open [f1]polarssl_cryptogram(key, KEY_BYTE_SIZE, key_cs, key_cg);
    //@ close exists(key_cg);
    if (aes_setkey_enc(&aes_context, key, 
        (unsigned int) KEY_BYTE_SIZE * 8) != 0) 
      abort();
    //@ close [f1]polarssl_cryptogram(key, KEY_BYTE_SIZE, key_cs, key_cg);
      
    //@ chars_to_integer(&iv_off);
    temp = (unsigned int) iv_off;
    /*@ open [f2]polarssl_public_message(sc_enc_polarssl_pub)
                                        (message, message_len, m_cs); @*/
    if (aes_crypt_cfb128(&aes_context, POLARSSL_AES_ENCRYPT, 
                         (unsigned int) message_len, &temp, iv, 
                         message, encrypted) != 0) abort();
    /*@ close [f2]polarssl_public_message(sc_enc_polarssl_pub)
                                         (message, message_len, m_cs); @*/           
    aes_free(&aes_context);
    //@ open aes_context(&aes_context);
  }
  //@ open  polarssl_cryptogram(encrypted, message_len, ?e_cs, ?e_cg);    
  /*@ assert e_cg == polarssl_encrypted(creator, key_id, m_cs, 
                                       append(chars_of_int(iv_val), iv_cs)); @*/
  /*@ polarssl_cryptograms_in_chars_upper_bound_from(m_cs, 
                polarssl_generated_public_cryptograms(sc_enc_polarssl_pub)); @*/
  //@ close sc_enc_polarssl_pub(e_cg);
  //@ leak sc_enc_polarssl_pub(e_cg);
  /*@ polarssl_generated_public_cryptograms_upper_bound(
                                                 sc_enc_polarssl_pub, e_cg); @*/
  memcpy(m + 20, encrypted, (unsigned int) message_len);
  //@ chars_join(m);
  //@ assert chars(m, 20 + message_len, ?cs2);
  /*@ polarssl_cryptograms_in_chars_public_upper_bound_join(
                                            sc_enc_polarssl_pub, cs1, e_cs); @*/
  //@ assert cs2 == append(cs1, e_cs);
  
  // calculate hmac
  {
    //@ open  [f1]polarssl_cryptogram(key, KEY_BYTE_SIZE, key_cs, key_cg);
    //@ close exists<polarssl_cryptogram>(key_cg);
    //@ assert chars(m, 20 + message_len, cs2);
    sha512_hmac(key, (unsigned int) KEY_BYTE_SIZE, m, 
                     (unsigned int) (20 + message_len), m + 20 + message_len, 0);
    //@ close [f1]polarssl_cryptogram(key, KEY_BYTE_SIZE, key_cs, key_cg);
  }
  //@ open polarssl_cryptogram(m + 20 + message_len, 64, ?h_cs, ?h_cg);
  
  //@ chars_join(m);
  //@ assert chars(m, 20 + message_len + 64, ?cs);
  //@ close exists<polarssl_cryptogram>(e_cg);
  //@ leak exists<polarssl_cryptogram>(e_cg);
  /*@ polarssl_cryptograms_in_chars_upper_bound_from(e_cs, 
                polarssl_generated_public_cryptograms(sc_enc_polarssl_pub)); @*/
  //@ close sc_enc_polarssl_pub(h_cg);
  //@ leak sc_enc_polarssl_pub(h_cg);
  /*@ polarssl_generated_public_cryptograms_upper_bound(
                                                 sc_enc_polarssl_pub, h_cg); @*/
  /*@ polarssl_cryptograms_in_chars_public_upper_bound_join(
                                            sc_enc_polarssl_pub, cs2, h_cs); @*/
  //@ append_assoc(append(chars_of_int(iv_off), iv_cs), e_cs, h_cs);
  //@ append_assoc(chars_of_int(iv_off), iv_cs, append(e_cs, h_cs));
  /*@ assert cs == append(chars_of_int(iv_off), 
                     append(iv_cs, append(e_cs, h_cs))); @*/
  
  /*@ close polarssl_public_message(sc_enc_polarssl_pub)
                                   (m, 20 + message_len + 64, 
                                   append(chars_of_int(iv_off), 
                                        append(iv_cs, append(e_cs, h_cs)))); @*/
  net_send(&socket, m, (unsigned int) 20 + (unsigned int) message_len + 64);
  //@ open polarssl_public_message(sc_enc_polarssl_pub)(m, _, _);
  
  {
    free(m);
    free(encrypted);
    havege_free(&havege_state);
    //@ open havege_state(&havege_state);
    net_close(socket);
  }
}

int app_receive(char *key, char **message)
  /*@ requires [?f0]polarssl_world<unit>(sc_enc_polarssl_pub,
                                         sc_enc_polarssl_proof_pred, 
                                         unit) &*&
               [?f1]polarssl_cryptogram(key, KEY_BYTE_SIZE, ?key_cs, ?key_cg) &*&
                 key_cg == polarssl_symmetric_key(?creator, ?key_id) &*&
               pointer(message, _);
  @*/
  /*@ ensures  [f0]polarssl_world<unit>(sc_enc_polarssl_pub,
                                        sc_enc_polarssl_proof_pred, 
                                        unit) &*&
               [f1]polarssl_cryptogram(key, KEY_BYTE_SIZE, key_cs, key_cg) &*&
               pointer(message, ?message_p) &*&
               malloc_block(message_p, result) &*&
               chars(message_p, result, ?m_cs) &*&
               bad(creator) ?
                 true == subset(polarssl_cryptograms_in_chars(m_cs),
                   polarssl_generated_public_cryptograms(sc_enc_polarssl_pub))
               : 
                 true == app_send_event(creator, m_cs);
  @*/
{
  int socket1;
  int socket2;
  int size;
  int result_size;
  char buffer[POLARSSL_MAX_MESSAGE_BYTE_SIZE];

  int iv_off;
  char iv[16];
  char hmac1[64];
  char hmac2[64];
  char* encrypted;
  char* decrypted;
  
  // Receive message
  if(net_bind(&socket1, NULL, APP_RECEIVE_PORT) != 0)
    abort();
  if(net_accept(socket1, &socket2, NULL) != 0)
    abort();
  if(net_set_block(socket2) != 0)
    abort();
    
  size = net_recv(&socket2, buffer, POLARSSL_MAX_MESSAGE_BYTE_SIZE);
  if (size < 20 + POLARSSL_MIN_ENCRYPTED_BYTE_SIZE + 64) abort();
  /*@ open polarssl_public_message(sc_enc_polarssl_pub)
                                  (buffer, size, ?cs); @*/
  //@ close [1/2]hide_chars(buffer, size, cs);
  result_size = size - 20 - 64;
  encrypted = malloc(result_size);
  if (encrypted == 0) abort();
  decrypted = malloc(result_size);
  if (decrypted == 0) abort();
  
  // Extract parts of message
  //@ chars_to_integer(buffer);
  iv_off = *((int*) buffer);
  //@ integer_to_chars(buffer);
  memcpy(iv, (void*) buffer + 4, 16);
  memcpy(encrypted, (void*) buffer + 20, (unsigned int) result_size);
  memcpy(hmac1, (void*) buffer + 20 + result_size, 64);
  //@ assert [1/2]chars(buffer, 4, ?off_cs);
  //@ assert chars(iv, 16, ?iv_cs);
  //@ assert chars(encrypted, result_size, ?e_cs);
  //@ assert chars(hmac1, 64, ?h_cs);
  //@ chars_join(buffer);
  //@ chars_join(buffer);
  //@ chars_join(buffer);
  //@ open [1/2]hide_chars(buffer, size, cs);
  //@ close [1/2]hide_chars(buffer, size, cs);
  //@ assert cs == append(off_cs, append(iv_cs, append(e_cs, h_cs)));
  //@ assert cs == append(append(append(off_cs, iv_cs), e_cs), h_cs);
   
  // Check hmac
  //@ open  [f1]polarssl_cryptogram(key, KEY_BYTE_SIZE, key_cs, key_cg);
  //@ close exists<polarssl_cryptogram>(key_cg);
  //@ assert [1/2]chars(buffer, 20 + result_size, ?hd_cs);
  //@ take_append(20 + result_size, append(append(off_cs, iv_cs), e_cs), h_cs);
  //@ drop_append(20 + result_size, append(append(off_cs, iv_cs), e_cs), h_cs);
  //@ append_assoc(off_cs, iv_cs, e_cs);
  //@ assert hd_cs == append(off_cs, append(iv_cs, e_cs));
  /*@ polarssl_cryptograms_in_chars_public_upper_bound_split(
                                 sc_enc_polarssl_pub, cs, 20 + result_size); @*/
  /*@ polarssl_cryptograms_in_chars_public_upper_bound_split(
                 sc_enc_polarssl_pub, hd_cs, length(append(off_cs, iv_cs))); @*/
  //@ drop_append(20, append(off_cs, iv_cs), e_cs);
  //@ assert [1/2]chars(buffer, 20 + result_size, hd_cs);
  sha512_hmac(key, (unsigned int) KEY_BYTE_SIZE, buffer, 
                    (unsigned int) (20 + result_size), hmac2, 0);
  //@ close [f1]polarssl_cryptogram(key, KEY_BYTE_SIZE, key_cs, key_cg);
  //@ open  polarssl_cryptogram(hmac2, 64, ?h2_cs, ?h_cg);
  if (memcmp(hmac1, hmac2, 64) != 0) abort();
  //@ assert h_cs == h2_cs;
  //@ assert h_cs == polarssl_chars_for_cryptogram(h_cg);
  //@ h_cg == polarssl_hmac(creator, key_id, hd_cs);
  
  /*@ {  
        polarssl_cryptogram_constraints(h_cs, h_cg);
        polarssl_cryptogram_in_upper_bound(h_cs, h_cg, 
                    polarssl_generated_public_cryptograms(sc_enc_polarssl_pub));
        polarssl_generated_public_cryptograms_from(sc_enc_polarssl_pub, h_cg);
        open [_]sc_enc_polarssl_pub(h_cg);
      }
  @*/
  
  // Decrypt message
  {
    unsigned int temp;
    aes_context aes_context;
    //@ close aes_context(&aes_context);
    //@ open [f1]polarssl_cryptogram(key, KEY_BYTE_SIZE, key_cs, key_cg);
    //@ close exists(key_cg);
    if (aes_setkey_enc(&aes_context, key, (unsigned int) KEY_BYTE_SIZE * 8) != 0) 
      abort();
    //@ assert aes_context_initialized(&aes_context, some(pair(creator, key_id)));
    //@ close [f1]polarssl_cryptogram(key, KEY_BYTE_SIZE, key_cs, key_cg);
    //@ assert hd_cs == append(append(off_cs, iv_cs), e_cs);

    //@ assert chars(encrypted, result_size, e_cs);
    if (iv_off < 0 || iv_off > 15) abort();
    temp = (unsigned int) iv_off;
    if (aes_crypt_cfb128(&aes_context, POLARSSL_AES_DECRYPT, 
                         (unsigned int) result_size,
                         &temp, iv, encrypted, decrypted) != 0) abort();
    aes_free(&aes_context);
    //@ open aes_context(&aes_context);
  }
  //@ assert chars(decrypted, result_size, ?dec_cs);
  /*@ polarssl_cryptogram e_cg = polarssl_encrypted(
                            creator, key_id, dec_cs, append(off_cs, iv_cs)); @*/
  //@ assert e_cs == polarssl_chars_for_cryptogram(e_cg);
  //@ polarssl_cryptogram_constraints(e_cs, e_cg);
  /*@ polarssl_cryptogram_in_upper_bound(e_cs, e_cg, 
                polarssl_generated_public_cryptograms(sc_enc_polarssl_pub)); @*/
  //@ polarssl_generated_public_cryptograms_from(sc_enc_polarssl_pub, e_cg);
  //@ open [_]sc_enc_polarssl_pub(e_cg);
  
  //@ chars_join(buffer);
  //@ chars_join(buffer);
  //@ open [1/2]hide_chars(buffer, size, cs);
  
  net_close(socket1);
  net_close(socket2);
  
  free(encrypted);
  *message = decrypted;
  return result_size;
  
  //@ assert chars(decrypted, result_size, dec_cs);
  /*@
    if (bad(creator))
    {
      assert true == subset(polarssl_cryptograms_in_chars(dec_cs),
               polarssl_generated_public_cryptograms(sc_enc_polarssl_pub));
    }
    else
    {
      assert true == app_send_event(creator, dec_cs);
    }
  @*/
}
