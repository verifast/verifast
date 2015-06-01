#ifndef RPC_H
#define RPC_H

#include "../../annotated_api/polarssl_definitions/polarssl_definitions.h"

#define PACKAGE_SIZE 40

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

predicate rpc_pub(cryptogram cg) =
  switch (cg)
  {
    case cg_random(p0, c0):
      return true;
    case cg_symmetric_key(p0, c0):
      return true == bad(p0);
    case cg_public_key(p0, c0):
      return true;
    case cg_private_key(p0, c0):
      return true == bad(p0);
    case cg_hash(cs0):
      return true;
    case cg_hmac(p0, c0, cs0):
      return
        true == bad(p0) || bad(shared_with(p0, c0)) ||
        switch (cs0) 
        {
          case cons(c1, cs1): return
            c1 == '0' ?
              request(p0, shared_with(p0, c0), cs1)
          : c1 == '1' ?
              response(p0, shared_with(p0, c0), take(PACKAGE_SIZE, cs1),
                                                drop(PACKAGE_SIZE, cs1))
          :
            false;
          case nil:
            return false;
        };
    case cg_encrypted(p0, c0, cs0, ent0):
      return [_]public_generated(rpc_pub)(cs0) &*&
             (bad(p0) || bad(shared_with(p0, c0)));
    case cg_auth_encrypted(p0, c0, mac0, cs0, ent0):
      return [_]public_generated(rpc_pub)(cs0) &*&
             (bad(p0) || bad(shared_with(p0, c0)));
    case cg_asym_encrypted(p0, c0, cs0, ent0):
      return [_]public_generated(rpc_pub)(cs0);
    case cg_asym_signature(p0, c0, cs0, ent0):
      return true == bad(p0);
  }
;

@*/

///////////////////////////////////////////////////////////////////////////////
// Implementation prototypes for this protocol ////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

void client(char *key, int key_len, char *request, char *response);
  /*@ requires [_]public_invar(rpc_pub) &*&
               [?f1]cryptogram(key, key_len, ?key_cs, ?key_cg) &*&
                 key_cg == cg_symmetric_key(?creator, ?id) &*&
               [?f2]chars(request, PACKAGE_SIZE, ?req_cs) &*&
               request(creator, shared_with(creator, id), req_cs) == true &*&
               chars(response, PACKAGE_SIZE, _); @*/
  /*@ ensures  [f1]cryptogram(key, key_len, key_cs, key_cg) &*&
               [f2]chars(request, PACKAGE_SIZE, req_cs) &*&
               chars(response, PACKAGE_SIZE, ?resp_cs) &*&
               bad(creator) || bad(shared_with(creator, id)) ||
               response(creator, shared_with(creator, id), req_cs, resp_cs); @*/

void server(char *key, int key_len);
  /*@ requires [_]public_invar(rpc_pub) &*&
               [?f1]cryptogram(key, key_len, ?key_cs, ?key_cg) &*&
                 key_cg == cg_symmetric_key(?creator, ?id) &*&
               generated_values(shared_with(creator, id), ?count); @*/
  /*@ ensures  [f1]cryptogram(key, key_len, key_cs, key_cg) &*&
               generated_values(shared_with(creator, id), count + 1); @*/

///////////////////////////////////////////////////////////////////////////////
// Attacker proof obligations for this protocol ///////////////////////////////
///////////////////////////////////////////////////////////////////////////////

//@ PUBLIC_INVARIANT_PROOFS(rpc)

#endif
