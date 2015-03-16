#include "secure_communication_authenticated_encryption.h"

#include "../../src/random.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

//@ #include <listex.gh>
//@ #include <quantifiers.gh>

#define APP_RECEIVE_PORT 121212

void app_send(char *key, char *message, int message_len)
  /*@ requires [?f0]polarssl_world(sc_auth_polarssl_pub) &*&
               [?f1]polarssl_cryptogram(key, KEY_BYTE_SIZE, ?key_cs, ?key_cg) &*&
                 key_cg == polarssl_symmetric_key(?creator, ?key_id) &*&
               [?f2]polarssl_public_message(sc_auth_polarssl_pub)
                                           (message, message_len, ?m_cs) &*&
                 message_len >= POLARSSL_MIN_ENCRYPTED_BYTE_SIZE &*&
                 message_len < POLARSSL_MAX_MESSAGE_BYTE_SIZE - 84 &*&
               polarssl_generated_values(creator, ?count1) &*&
               true == app_send_event(creator, m_cs);
  @*/
  /*@ ensures  [f0]polarssl_world(sc_auth_polarssl_pub) &*&
               [f1]polarssl_cryptogram(key, KEY_BYTE_SIZE, key_cs, key_cg) &*&
               [f2]polarssl_public_message(sc_auth_polarssl_pub)
                                          (message, message_len, m_cs) &*&
               polarssl_generated_values(creator, ?count2) &*&
               count2 > count1;
  @*/
{
  int socket;
  havege_state havege_state;
  char iv[16];

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
    //@ close random_request(creator, 0, false);
    if (havege_random(&havege_state, iv, 16) != 0) abort();  
  }
  //@ open polarssl_cryptogram(iv, 16, ?iv_cs, _);

  char* m = malloc(16 + message_len + 16);
  if (m == 0) abort();
  memcpy(m, iv, 16);
  //@ assert chars(m, 16, iv_cs);
  //@ assert chars(m + 16, message_len + 16, ?cs1);
  //@ polarssl_public_generated_chars_assume(sc_auth_polarssl_pub, iv_cs);
   
  // encrypt message
  {
    unsigned int temp;
    gcm_context gcm_context;
    //@ close gcm_context(&gcm_context);
    //@ open [f1]polarssl_cryptogram(key, KEY_BYTE_SIZE, key_cs, key_cg);
    //@ close polarssl_key_id(creator, key_id);
    if (gcm_init(&gcm_context, POLARSSL_AES_CIPHER_ID, key, 
                (unsigned int) KEY_BYTE_SIZE * 8) != 0) abort();
    //@ close [f1]polarssl_cryptogram(key, KEY_BYTE_SIZE, key_cs, key_cg);

    /*@ open [f2]polarssl_public_message(sc_auth_polarssl_pub)
                                        (message, message_len, m_cs); @*/
    //@ chars_split(m + 16, message_len);
    if (gcm_crypt_and_tag(&gcm_context, POLARSSL_GCM_ENCRYPT, 
                          (unsigned int) message_len,
                          iv, 16, NULL, 0, message, m + 16, 16,
                          (char*) ((m + 16) + message_len)) != 0)
      abort();
    /*@ close [f2]polarssl_public_message(sc_auth_polarssl_pub)
                                         (message, message_len, m_cs); @*/
    gcm_free(&gcm_context);
    //@ open gcm_context(&gcm_context);
  }
  //@ assert polarssl_cryptogram(m + 16, message_len, ?e_cs, ?e_cg);
  /*@ assert e_cg == polarssl_auth_encrypted(
                                       creator, key_id, ?t_cs, m_cs, iv_cs); @*/
  //@ close sc_auth_polarssl_pub(e_cg);
  //@ leak sc_auth_polarssl_pub(e_cg);
  /*@ polarssl_public_message_from_cryptogram(
                     sc_auth_polarssl_pub, m + 16, message_len, e_cs, e_cg); @*/
  /*@ open polarssl_public_message(sc_auth_polarssl_pub)
                                  (m + 16, message_len, e_cs); @*/
  //@ assert chars(m + 16 + message_len, 16, t_cs);
  //@ chars_join(m);
  //@ chars_join(m);
  //@ assert chars(m, 16 + message_len + 16, ?cs);
  //@ append_assoc(iv_cs, e_cs, t_cs);
  //@ assert cs == append(iv_cs, append(e_cs, t_cs));
  
  //@ polarssl_public_generated_chars_assume(sc_auth_polarssl_pub, t_cs);
  
  ///*@ polarssl_generated_public_cryptograms_upper_bound(
  //                                              sc_auth_polarssl_pub, e_cg); 
  /*@ polarssl_public_generated_chars_join(
                                         sc_auth_polarssl_pub, iv_cs, e_cs); @*/
  /*@ polarssl_public_generated_chars_join(
                           sc_auth_polarssl_pub, append(iv_cs, e_cs), t_cs); @*/
  /*@ close polarssl_public_message(sc_auth_polarssl_pub)
                                   (m, 16 + message_len + 16,
                                    append(iv_cs, append(e_cs, t_cs))); @*/
  net_send(&socket, m, (unsigned int) 16 + (unsigned int) message_len + 16);
  //@ open polarssl_public_message(sc_auth_polarssl_pub)(m, _, _);

  {
    free(m);
    havege_free(&havege_state);
    //@ open havege_state(&havege_state);
    net_close(socket);
  }
}

int app_receive(char *key, char **message)
  /*@ requires [?f0]polarssl_world(sc_auth_polarssl_pub) &*&
               [?f1]polarssl_cryptogram(key, KEY_BYTE_SIZE, ?key_cs, ?key_cg) &*&
                 key_cg == polarssl_symmetric_key(?creator, ?key_id) &*&
               pointer(message, _);
  @*/
  /*@ ensures  [f0]polarssl_world(sc_auth_polarssl_pub) &*&
               [f1]polarssl_cryptogram(key, KEY_BYTE_SIZE, key_cs, key_cg) &*&
               pointer(message, ?message_p) &*&
               malloc_block(message_p, result) &*&
               chars(message_p, result, ?m_cs) &*&
               bad(creator) ?
                 [_]polarssl_public_generated_chars(sc_auth_polarssl_pub)(m_cs)
               : 
                 true == app_send_event(creator, m_cs);
  @*/
{
  int socket1;
  int socket2;
  int size;
  int result_size;
  char buffer[POLARSSL_MAX_MESSAGE_BYTE_SIZE];

  char iv[16];
  char tag[16];
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
  if (size < 16 + POLARSSL_MIN_ENCRYPTED_BYTE_SIZE + 16)
    abort();
  //@ open polarssl_public_message(sc_auth_polarssl_pub)(buffer, size, ?cs);
  //@ close [1/2]hide_chars(buffer, size, cs);
  result_size = size - 16 - 16;
  encrypted = malloc(result_size);
  if (encrypted == 0) abort();
  decrypted = malloc(result_size);
  if (decrypted == 0) abort();
  
  // Extract parts of message
  memcpy(iv, buffer, 16);
  memcpy(encrypted, (void*) buffer + 16, (unsigned int) result_size);
  memcpy(tag, (void*) buffer + 16 + result_size, 16);
  //@ assert chars(iv, 16, ?iv_cs);
  //@ assert chars(encrypted, result_size, ?e_cs);
  //@ assert chars(tag, 16, ?t_cs);
  //@ chars_join(buffer);
  //@ chars_join(buffer);
  //@ open [1/2]hide_chars(buffer, size, cs);
  //@ close [1/2]hide_chars(buffer, size, cs);
  //@ assert cs == append(iv_cs, append(e_cs, t_cs));

  // Decrypt message
  {
    gcm_context gcm_context;
    //@ close gcm_context(&gcm_context);
    //@ open [f1]polarssl_cryptogram(key, KEY_BYTE_SIZE, key_cs, key_cg);
    //@ close polarssl_key_id(creator, key_id);
    if (gcm_init(&gcm_context, POLARSSL_AES_CIPHER_ID, key, 
                (unsigned int) KEY_BYTE_SIZE * 8) != 0) abort();
    /*@ assert gcm_context_initialized(&gcm_context, 
                                       some(pair(creator, key_id))); @*/
    //@ close [f1]polarssl_cryptogram(key, KEY_BYTE_SIZE, key_cs, key_cg);

    //@ polarssl_public_generated_chars_split(sc_auth_polarssl_pub, cs, 16);
    /*@ polarssl_public_generated_chars_split(
                     sc_auth_polarssl_pub, append(e_cs, t_cs), result_size); @*/
    //@ assert chars(encrypted, result_size, e_cs);
    if (gcm_auth_decrypt(&gcm_context, (unsigned int) result_size,
                         iv, 16, NULL, 0, tag, 16,
                         encrypted, decrypted) != 0) abort();
    gcm_free(&gcm_context);
    //@ open gcm_context(&gcm_context);
  }
  
  //@ assert chars(decrypted, result_size, ?dec_cs);
  //@ chars_join(buffer);
  //@ open [1/2]hide_chars(buffer, size, cs);

  /*@ polarssl_cryptogram e_cg = polarssl_auth_encrypted(
                                      creator, key_id, t_cs, dec_cs, iv_cs); @*/
  //@ assert e_cs == polarssl_chars_for_cryptogram(e_cg);
  //@ polarssl_cryptogram_constraints(e_cs, e_cg);
  /*@ polarssl_public_generated_chars_extract(
                                          sc_auth_polarssl_pub, e_cs, e_cg); @*/
  //@ open [_]sc_auth_polarssl_pub(e_cg);
  /*@ if (!bad(creator))
      {
        assert true == app_send_event(creator, dec_cs);
      }
      else
      {
        assert [_]polarssl_public_generated_chars(sc_auth_polarssl_pub)(dec_cs);
      }
  @*/

  net_close(socket1);
  net_close(socket2);
  
  free(encrypted);
  *message = decrypted;
  return result_size;
}
