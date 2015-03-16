#ifndef RPC_H
#define RPC_H

#include "../../annotated_api/polarssl.h"
//@ #include "../../annotated_api/proof_obligations.gh"

#define PACKAGE_BYTE_SIZE 40

///////////////////////////////////////////////////////////////////////////////
// Encodings for this protocol ////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

/*@
fixpoint int shared_with(int cl, int id);

fixpoint bool request(int cl, int sv, list<char> req);
fixpoint bool response(int cl, int sv, list<char> req, list<char> resp);

///////////////////////////////////////////////////////////////////////////////
// Definition of pub for this protocol ////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

predicate rpc_polarssl_pub(polarssl_cryptogram cg) =
  switch (cg)
  {
    case polarssl_random(p0, c0):
      return true == bad(p0) || bad(shared_with(p0, c0));
    case polarssl_symmetric_key(p0, c0):
      return true == bad(p0);
    case polarssl_public_key(p0, c0):
      return true;
    case polarssl_private_key(p0, c0):
      return true == bad(p0);
    case polarssl_hash(cs0):
      return true;
    case polarssl_hmac(p0, c0, cs0):
      return
        true == bad(p0) || bad(shared_with(p0, c0)) ||
        switch (cs0) 
        {
          case cons(c1, cs1): return
            c1 == '0' ?
              request(p0, shared_with(p0, c0), cs1)
          : c1 == '1' ?
              response(p0, shared_with(p0, c0), take(PACKAGE_BYTE_SIZE, cs1),
                                                drop(PACKAGE_BYTE_SIZE, cs1))
          :
            false;
          case nil:
            return false;
        };
    case polarssl_encrypted(p0, c0, cs0, ent0):
      return [_]polarssl_public_generated_chars(rpc_polarssl_pub)(cs0) &*&
             (bad(p0) || bad(shared_with(p0, c0)));
    case polarssl_auth_encrypted(p0, c0, mac0, cs0, ent0):
      return [_]polarssl_public_generated_chars(rpc_polarssl_pub)(cs0) &*&
             (bad(p0) || bad(shared_with(p0, c0)));
    case polarssl_asym_encrypted(p0, c0, cs0, ent0):
      return [_]polarssl_public_generated_chars(rpc_polarssl_pub)(cs0);
    case polarssl_asym_signature(p0, c0, cs0, ent0):
      return true == bad(p0);
  }
;

@*/

///////////////////////////////////////////////////////////////////////////////
// Implementation prototypes for this protocol ////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

void client(char *key, int key_len, char *request, char *response);
  /*@ requires [?f0]polarssl_world(rpc_polarssl_pub) &*&
               [?f1]polarssl_cryptogram(key, key_len, ?key_cs, ?key_cg) &*&
                 key_cg == polarssl_symmetric_key(?creator, ?id) &*&
               [?f2]polarssl_public_message(rpc_polarssl_pub)
                                           (request, PACKAGE_BYTE_SIZE, ?req_cs) &*&
               request(creator, shared_with(creator, id), req_cs) == true &*&
               chars(response, PACKAGE_BYTE_SIZE, _);
  @*/
  /*@ ensures  [f0]polarssl_world(rpc_polarssl_pub) &*&
               [f1]polarssl_cryptogram(key, key_len, key_cs, key_cg) &*&
               [f2]polarssl_public_message(rpc_polarssl_pub)
                                          (request, PACKAGE_BYTE_SIZE, req_cs) &*&
               polarssl_public_message(rpc_polarssl_pub)
                                      (response, PACKAGE_BYTE_SIZE, ?resp_cs) &*&
               bad(creator) || bad(shared_with(creator, id)) ?
                 true
               :
                 response(creator, shared_with(creator, id), req_cs, resp_cs) == true;
  @*/

void server(char *key, int key_len);
  /*@ requires [?f0]polarssl_world(rpc_polarssl_pub) &*&
               [?f1]polarssl_cryptogram(key, key_len, ?key_cs, ?key_cg) &*&
                 key_cg == polarssl_symmetric_key(?creator, ?id) &*&
               polarssl_generated_values(shared_with(creator, id), ?count);
  @*/
  /*@ ensures  [f0]polarssl_world(rpc_polarssl_pub) &*&
               [f1]polarssl_cryptogram(key, key_len, key_cs, key_cg) &*&
               polarssl_generated_values(shared_with(creator, id), count + 1);
  @*/

///////////////////////////////////////////////////////////////////////////////
// Attacker proof obligations for this protocol ///////////////////////////////
///////////////////////////////////////////////////////////////////////////////

//@ POLARSSL_PROOFS_DEFAULT(rpc, 1)

#endif
