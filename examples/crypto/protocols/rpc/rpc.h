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

// The example protocol uses two event predicates: "request(C, S, R)" states that
// client C sent a request item R to server S; "response(C, S, R, R1)" states that
// server S responded to request item R from client C with response item R1.

fixpoint bool request(int cl, int sv, item req);
fixpoint bool response(int cl, int sv, item req, item resp);

///////////////////////////////////////////////////////////////////////////////
// Definition of pub for this protocol ////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

fixpoint bool rpc_pub(item i)
{
  switch (i)
  {
    case key_item(p0, c0, k0, i0):
      return bad(p0) || bad(shared_with(p0, c0));
    case data_item(d0): return true;
    case hmac_item(k0, m0): return
      switch (k0) 
      {
        case key_item(creator0, count0, kind0, info0) : return
          bad(creator0) || 
          bad(shared_with(creator0, count0)) ||
          collision_in_run() ||
          switch (m0) {
            case pair_item(first1, second1): return
              switch (first1) {
                case data_item(tag2): return
                  tag2 == 0 ?
                    request(creator0, shared_with(creator0, count0), second1)
                  : tag2 == 1 ?
                    switch (second1) {
                      case pair_item(req3, resp3): return
                        response(creator0, 
                                 shared_with(creator0, count0), req3, resp3);
                      default: return false;
                    }
                  : false
                    ;
                default: return false;
              };
            default: return false;
          };  
        default: return false;
      };
    case pair_item(first0, second0):
      return rpc_pub(first0) && rpc_pub(second0);
    case nonce_item(p0, c0, inc0, info0): 
      return bad(p0);
    case encrypted_item(k0, p0, e0): return
      switch (k0) 
      {
        case key_item(creator1, count1, kind1, info1) : return
          (rpc_pub(k0) && rpc_pub(p0)) || collision_in_run();
        default: return true;
      };
  }
}

@*/

///////////////////////////////////////////////////////////////////////////////
// Implementation prototypes for this protocol ////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

struct item *client(int server, struct item *key, struct item *request);
  /*@ requires [?f0]world(rpc_pub) &*&
               item(key, 
                    key_item(?creator, ?id, symmetric_key, int_pair(0, 0))) &*&
               item(request, ?req) &*& rpc_pub(req) == true &*& 
               request(creator, server, req) == true &*&
               shared_with(creator, id) == server;
  @*/
  /*@ ensures  [f0]world(rpc_pub) &*&
               item(key, 
                    key_item(creator, id, symmetric_key, int_pair(0, 0))) &*&
               item(request, req) &*& item(result, ?resp) &*& 
               (
                 bad(creator) || 
                 bad(server) ||
                 collision_in_run() ||
                 response(creator, server, req, resp) == true
               );
  @*/

void server(int server, struct item *key);
  /*@ requires [?f0]world(rpc_pub) &*&
               generated_values(server, ?count) &*&
               item(key, key_item(?creator, ?id, symmetric_key, ?info)) &*&  
               shared_with(creator, id) == server;
  @*/
  /*@ ensures  [f0]world(rpc_pub) &*&
               generated_values(server, count + 1) &*&
               item(key, key_item(creator, id, symmetric_key, info));
  @*/

///////////////////////////////////////////////////////////////////////////////
// Attacker proof obligations for this protocol ///////////////////////////////
///////////////////////////////////////////////////////////////////////////////

//@ ATTACKER_PROOFS_DEFAULT(rpc)

#endif
