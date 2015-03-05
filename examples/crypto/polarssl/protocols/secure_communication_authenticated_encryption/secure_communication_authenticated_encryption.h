#ifndef SECURE_COMMUNICATION_AUTHENTICATION_ENCRYPTION_H
#define SECURE_COMMUNICATION_AUTHENTICATION_ENCRYPTION_H

#include "../../annotated_api/polarssl.h"
//@ #include "../../annotated_api/proof_obligations.gh"

#include "string.h"

#define NONCE_BYTE_SIZE  64
#define KEY_BYTE_SIZE    16

/*

Dolev-Yao security verification of a simple secure communication protocol

*/

///////////////////////////////////////////////////////////////////////////////
// Encodings for this protocol ////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

/*@
fixpoint bool app_send_event(int sender, list<char> message);

///////////////////////////////////////////////////////////////////////////////
// Definition of pub for this protocol ////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

predicate sc_auth_polarssl_pub(polarssl_cryptogram cg) =
  switch (cg)
  {
    case polarssl_random(p1, c1):
      return true == bad(p1);
    case polarssl_symmetric_key(p1, c1):
      return true == bad(p1);
    case polarssl_public_key(p1, c1):
      return true;
    case polarssl_private_key(p1, c1):
      return true == bad(p1);
    case polarssl_hash(cs1):
      return true;
    case polarssl_hmac(p1, c1, cs1):
      return true == bad(p1);
    case polarssl_encrypted(p1, c1, cs1, ent1):
      return true == subset(polarssl_cryptograms_in_chars(cs1),
                   polarssl_generated_public_cryptograms(sc_auth_polarssl_pub));
    case polarssl_auth_encrypted(p1, c1, mac1, cs1, ent1):
      return bad(p1) ?
               true == subset(polarssl_cryptograms_in_chars(cs1),
                    polarssl_generated_public_cryptograms(sc_auth_polarssl_pub))
             :
               true == app_send_event(p1, cs1);
    case polarssl_asym_encrypted(p1, c1, cs1, ent1):
      return true == subset(polarssl_cryptograms_in_chars(cs1),
                   polarssl_generated_public_cryptograms(sc_auth_polarssl_pub));
    case polarssl_asym_signature(p1, c1, cs1, ent1): 
      return true == bad(p1);
  }
;

@*/

///////////////////////////////////////////////////////////////////////////////
// Implementation prototypes for this protocol ////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

void app_send(char *key, char *message, int message_len);
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

int app_receive(char *key, char **message);
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
                 true == subset(polarssl_cryptograms_in_chars(m_cs),
                   polarssl_generated_public_cryptograms(sc_auth_polarssl_pub))
               : 
                 true == app_send_event(creator, m_cs);
  @*/

///////////////////////////////////////////////////////////////////////////////
// Attacker proof obligations for this protocol ///////////////////////////////
///////////////////////////////////////////////////////////////////////////////

//@ POLARSSL_PROOFS_DEFAULT(sc_auth, 1)

#endif
