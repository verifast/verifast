#ifndef SECURE_STORAGE_H
#define SECURE_STORAGE_H

#include "../../annotated_api/polarssl.h"
//@ #include "../../annotated_api/proof_obligations.gh"

#include "string.h"

/*

Dolev-Yao security verification of a simple secure storage protocol

*/

///////////////////////////////////////////////////////////////////////////////
// Encodings for this protocol ////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

/*@
fixpoint bool app_send_event(int sender, list<char> message);

///////////////////////////////////////////////////////////////////////////////
// Definition of pub for this protocol ////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

predicate ss_polarssl_pub(polarssl_cryptogram cg) =
  switch(cg)
  {
    case polarssl_random(p0, c0):
      return true == bad(p0);
    case polarssl_symmetric_key(p0, c0):
      return true == bad(p0);
    case polarssl_public_key(p0, c0):
      return true;
    case polarssl_private_key(p0, c0):
      return true == bad(p0);
    case polarssl_hash(cs0):
      return true;
    case polarssl_hmac(p0, c0, cs0):
      return bad(p0) || app_send_event(p0, cs0);
    case polarssl_encrypted(p0, c0, cs0, ent0):
      return [_]polarssl_public_generated_chars(ss_polarssl_pub)(cs0) &*&
             true == bad(p0);
    case polarssl_auth_encrypted(p0, c0, mac0, cs0, ent0):
      return [_]polarssl_public_generated_chars(ss_polarssl_pub)(cs0) &*&
             true == bad(p0);
    case polarssl_asym_encrypted(p0, c0, cs0, ent0):
      return [_]polarssl_public_generated_chars(ss_polarssl_pub)(cs0);
    case polarssl_asym_signature(p0, c0, cs0, ent0):
        return true == bad(p0);
  }
;


@*/

///////////////////////////////////////////////////////////////////////////////
// Implementation prototypes for this protocol ////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

void app_send(char *key, int key_len, char *message, int message_len);
  /*@ requires [?f0]polarssl_world(ss_polarssl_pub) &*&
               [?f1]polarssl_cryptogram(key, key_len, ?key_cs, ?key_cg) &*&
                 key_cg == polarssl_symmetric_key(?creator, ?id) &*&
               [?f2]polarssl_public_message(ss_polarssl_pub)
                                           (message, message_len, ?msg_cs) &*&
                 message_len >= POLARSSL_MIN_HMAC_INPUT_BYTE_SIZE &*&
                 message_len < POLARSSL_MAX_MESSAGE_BYTE_SIZE - 64 &*&
               app_send_event(creator, msg_cs) == true;
  @*/
  /*@ ensures  [f0]polarssl_world(ss_polarssl_pub) &*&
               [f1]polarssl_cryptogram(key, key_len, key_cs, key_cg) &*&
               [f2]polarssl_public_message(ss_polarssl_pub)
                                          (message, message_len, msg_cs);
  @*/

int app_receive(char *key, int key_len, char **message);
  /*@ requires [?f0]polarssl_world(ss_polarssl_pub) &*&
               [?f1]polarssl_cryptogram(key, key_len, ?key_cs, ?key_cg) &*&
                 key_cg == polarssl_symmetric_key(?creator, ?id) &*&
               pointer(message, _);
  @*/
  /*@ ensures  [f0]polarssl_world(ss_polarssl_pub) &*&
               [f1]polarssl_cryptogram(key, key_len, key_cs, key_cg) &*&
               pointer(message, ?message_p) &*&
                 malloc_block(message_p, result) &*&
                 polarssl_public_message(ss_polarssl_pub)
                                        (message_p, result, ?msg_cs) &*&
                 bad(creator) ? true : true == app_send_event(creator, msg_cs);
  @*/

///////////////////////////////////////////////////////////////////////////////
// Attacker proof obligations for this protocol ///////////////////////////////
///////////////////////////////////////////////////////////////////////////////

//@ POLARSSL_PROOFS_DEFAULT(ss, 1)

#endif
