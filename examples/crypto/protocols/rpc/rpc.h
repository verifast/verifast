#ifndef RPC_H
#define RPC_H

// See explanations in ../../includes/cryptolib.h
#include "../../include/cryptolib.h"

/*
Dolev-Yao security verification of a simple request-response protocol.

This protocol performs RPC between pairs of clients and servers that have agreed
on a secret key. The key agreement mechanism is not modeled; it is assumed that
client and server share a secret key. Specifically, we declare a function
shared_with(P, N) that takes a principal P and an index N and that returns the
principal with whom the Nth key created by P is shared, or -1 if the key was not
shared. We assume the client generated the key and shared it with the server.
*/

///////////////////////////////////////////////////////////////////////////////
// Encodings for this protocol ////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

/*@
fixpoint int shared_with(int cl, int id);

// The example protocol uses two event predicates: "request(C, S, R)" states 
// that client C sent a request item R to server S; "response(C, S, R, R1)" 
// states that server S responded to request item R from client C with response 
// item R1.

fixpoint bool request(int cl, int sv, item req);
fixpoint bool response(int cl, int sv, item req, item resp);

///////////////////////////////////////////////////////////////////////////////
// Definition of pub for this protocol ////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

predicate rpc_pub(item i) =
  collision_in_run() ? true :
  [_]info_for_item(i, ?info0) &*&
  switch (i) 
  {
    case data_item(d0):
      return true;
    case pair_item(f0, s0):
      return [_]rpc_pub(f0) &*& 
             [_]rpc_pub(s0);
    case nonce_item(p0, c0, inc0): 
      return true == bad(p0);
    case hash_item(pay0): return
      switch (pay0)
      {
        case some(pay1):
          return [_]rpc_pub(pay1);
        case none:
          return true;
      };
    case symmetric_key_item(p0, c0):
      return true == bad(p0) || bad(shared_with(p0, c0));
    case public_key_item(p0, c0):
      return true;
    case private_key_item(p0, c0):
      return true == bad(p0);
    case hmac_item(p0, c0, pay0): return
      switch(pay0)
      {
        case some(pay1): return
          bad(p0) || 
          bad(shared_with(p0, c0)) ||
          switch (pay1) {
            case pair_item(first2, second2): return
              switch (first2) {
                case data_item(tag3): return
                  tag3 == cons(0, nil) ?
                    request(p0, shared_with(p0, c0), second2)
                : tag3 == cons(1, nil) ?
                    switch (second2) 
                    {
                      case pair_item(req4, resp4): return
                        response(p0, shared_with(p0, c0), req4, resp4);
                      default: return false;
                    }
                : false;
                default: return false;
              };
            default: return false;
          };
        case none:
          return true;
      };
    case symmetric_encrypted_item(p0, c0, pay0, ent0): return
      switch(pay0)
      {
        case some(pay1):
          return [_]rpc_pub(pay1);
        case none:
          return true;
      };
    case asymmetric_encrypted_item(p0, c0, pay0, ent0): return
      switch (pay0)
      {
        case some(pay1): return
          [_]message_tag(i)(?tag) &*& 
          tag == 10 ?
          (
            [_]rpc_pub(pay1)
          ) :
          false;
        case none:
          return true;
      };
    case asymmetric_signature_item(p0, c0, pay0, ent0): return
      switch (pay0)
      {
        case some(pay1):
          return [_]rpc_pub(pay1);
        case none:
          return true;
      };
  }
;

@*/

///////////////////////////////////////////////////////////////////////////////
// Implementation prototypes for this protocol ////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

struct item *client(char server, struct item *key, struct item *request);
  /*@ requires [?f0]world(rpc_pub) &*&
               item(key, symmetric_key_item(?creator, ?id), rpc_pub) &*&
               item(request, ?req, rpc_pub) &*& [_]rpc_pub(req) &*&
               true == well_formed_item(req) &*&
               true == request(creator, server, req) &*&
               shared_with(creator, id) == server;
  @*/
  /*@ ensures  [f0]world(rpc_pub) &*&
               item(key, symmetric_key_item(creator, id), rpc_pub) &*&
               item(request, req, rpc_pub) &*& item(result, ?resp, rpc_pub) &*& 
               (
                 bad(creator) || 
                 bad(server) ||
                 collision_in_run() ||
                 true == response(creator, server, req, resp) == true
               );
  @*/

void server(char server, struct item *key);
  /*@ requires [?f0]world(rpc_pub) &*&
               generated_values(server, ?count) &*&
               item(key, symmetric_key_item(?creator, ?id), rpc_pub) &*&  
               shared_with(creator, id) == server;
  @*/
  /*@ ensures  [f0]world(rpc_pub) &*&
               generated_values(server, count + 1) &*&
               item(key, symmetric_key_item(creator, id), rpc_pub);
  @*/

///////////////////////////////////////////////////////////////////////////////
// Attacker proof obligations for this protocol ///////////////////////////////
///////////////////////////////////////////////////////////////////////////////

//@ PROOFS_DEFAULT(rpc)

#endif
