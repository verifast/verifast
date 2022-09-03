#ifndef RPC_H
#define RPC_H

#include "../../annotated_api/mbedTLS_definitions.h"

#define PACKAGE_SIZE 40

/*@

// 1. client -> server : {request, HMAC(K, request)}
// 2. server -> client : {request, respons, HMAC(K, {request, response})}

///////////////////////////////////////////////////////////////////////////////
// Encodings for this protocol ////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

fixpoint int shared_with(int cl, int id);

fixpoint bool request(int cl, int sv, list<char> req);
fixpoint bool response(int cl, int sv, list<char> req, list<char> resp);

///////////////////////////////////////////////////////////////////////////////
// Definition of pub for this protocol ////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

predicate rpc_proof_pred() = true;

fixpoint bool rpc_public_key(int p, int c, bool symmetric)
{
  return bad(p);
}

predicate rpc_pub(cryptogram cg) =
  switch (cg)
  {
    case cg_nonce(p0, c0):
      return true;
    case cg_symmetric_key(p0, c0):
      return true == rpc_public_key(p0, c0, true);
    case cg_rsa_public_key(p0, c0):
      return true;
    case cg_rsa_private_key(p0, c0):
      return true == rpc_public_key(p0, c0, false);
    case cg_sha512_hash(ccs0):
      return true;
    case cg_sha512_hmac(p0, c0, ccs0):
      return rpc_public_key(p0, c0, true) ? true :
        exists(?cs0) &*& ccs0 == cs_to_ccs(cs0) &*&
        switch (cs0)
        {
          case cons(c1, cs1): return
            c1 == '0' ?
              true == request(p0, shared_with(p0, c0), cs1)
          : c1 == '1' ?
              bad(shared_with(p0, c0)) ||
              response(p0, shared_with(p0, c0), take(PACKAGE_SIZE, cs1),
                                                drop(PACKAGE_SIZE, cs1))
          :
            false;
          case nil:
            return false;
        };
    case cg_aes_encrypted(p0, c0, ccs0, ent0):
      return true == rpc_public_key(p0, c0, true) &*&
             [_]public_ccs(ccs0);
    case cg_aes_auth_encrypted(p0, c0, ccs0, ent0):
      return true == rpc_public_key(p0, c0, true) &*&
             [_]public_ccs(ccs0);
    case cg_rsa_encrypted(p0, c0, ccs0, ent0):
      return [_]public_ccs(ccs0);
    case cg_rsa_signature(p0, c0, ccs0, ent0):
      return true == rpc_public_key(p0, c0, false);
  }
;

@*/

///////////////////////////////////////////////////////////////////////////////
// Implementation prototypes for this protocol ////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

void client(char *key, int key_len, char *request, char *response);
  /*@ requires [_]public_invar(rpc_pub) &*&
               principal(?client, _) &*&
               [?f1]cryptogram(key, key_len, ?key_ccs, ?key_cg) &*&
                 key_cg == cg_symmetric_key(client, ?id) &*&
               [?f2]chars(request, PACKAGE_SIZE, ?req_cs) &*&
                 bad(client) ||
                 request(client, shared_with(client, id), req_cs) == true &*&
               chars_(response, PACKAGE_SIZE, _); @*/
  /*@ ensures  principal(client, _) &*&
               [f1]cryptogram(key, key_len, key_ccs, key_cg) &*&
               [f2]chars(request, PACKAGE_SIZE, req_cs) &*&
               chars(response, PACKAGE_SIZE, ?resp_cs) &*&
                 col || bad(client) || bad(shared_with(client, id)) ||
                 response(client, shared_with(client, id),
                          req_cs, resp_cs); @*/

void server(char *key, int key_len, char *request, char *response);
  /*@ requires [_]public_invar(rpc_pub) &*&
               principal(?server, _) &*&
               [?f1]cryptogram(key, key_len, ?key_ccs, ?key_cg) &*&
                 key_cg == cg_symmetric_key(?client, ?id) &*&
                 server == shared_with(client, id) &*&
               chars_(request, PACKAGE_SIZE, _) &*&
               chars_(response, PACKAGE_SIZE, _); @*/
  /*@ ensures  principal(server, _) &*&
               [f1]cryptogram(key, key_len, key_ccs, key_cg) &*&
               chars(request, PACKAGE_SIZE, ?req_cs) &*&
                 col || bad(client) ||
                 request(client, server, req_cs) &*&
               chars(response, PACKAGE_SIZE, ?resp_cs) &*&
                 col || bad(client) || bad(server) ||
                 response(client, server, req_cs, resp_cs); @*/

///////////////////////////////////////////////////////////////////////////////
// Attacker proof obligations for this protocol ///////////////////////////////
///////////////////////////////////////////////////////////////////////////////

//@ PUBLIC_INVARIANT_PROOFS(rpc)
//@ DECRYPTION_PROOFS(rpc)

#endif
