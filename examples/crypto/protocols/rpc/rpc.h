#ifndef RPC_H
#define RPC_H

// See explanations in ../../lib/dolevyao.h
#include "dolevyao.h"
#include "attacker.h"

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
    case key_item(p0, c0, k0, i0): return bad(p0) || bad(shared_with(p0, c0));
    case data_item(d0): return true;
    case hmac_item(creator0, count0, kind0, info0, m0): return
      bad(creator0) || bad(shared_with(creator0, count0))
      ||
      switch (m0) {
        case pair_item(first1, second1): return
          switch (first1) {
            case data_item(tag2): return
              tag2 == 0 ?
                request(creator0, shared_with(creator0, count0), second1)
              : tag2 == 1 ?
                switch (second1) {
                  case pair_item(req3, resp3): return
                    response(creator0, shared_with(creator0, count0), req3, resp3);
                  default: return false;
                }
              : false
                ;
            default: return false;
          };
        default: return false;
      };
    case encrypted_item(s0, count0, kind0, info0, p0, entropy0): 
      return (bad(s0) || bad(shared_with(s0, count0))) && rpc_pub(p0);
    case pair_item(first0, second0): 
      return rpc_pub(first0) && rpc_pub(second0);
    default: return false;
  }
}

@*/

///////////////////////////////////////////////////////////////////////////////
// Implementation prototypes for this protocol ////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

/*@ 
predicate protocol_pub(; fixpoint(item, bool) pub);

lemma void init_protocol();
     requires true;
     ensures protocol_pub(rpc_pub);
@*/

struct item *client(int server, struct item *key, struct item *request);
  /*@ requires [?f0]world(rpc_pub) &*& [?f1]net_api_initialized() &*&
               key_item(key, ?creator, ?id, symmetric_key, int_pair(0, 0)) &*& 
               item(request, ?req) &*&
               rpc_pub(req) == true &*& request(creator, server, req) == true &*& 
               shared_with(creator, id) == server; 
  @*/
  /*@ ensures  [f0]world(rpc_pub) &*& [f1]net_api_initialized() &*&
               key_item(key, creator, id, symmetric_key, int_pair(0, 0)) &*& 
               item(request, req) &*& 
               item(result, ?resp) &*& bad(creator) || bad(server) || 
               response(creator, server, req, resp) == true;  
  @*/

void server(int serverId, struct item *key);
  /*@ requires [?f0]world(rpc_pub) &*& [?f1]net_api_initialized() &*&
               key_item(key, ?creator, ?id, symmetric_key, ?info) &*& 
               shared_with(creator, id) == serverId; 
  @*/
  /*@ ensures  [f0]world(rpc_pub) &*& [f1]net_api_initialized() &*&
               key_item(key, creator, id, symmetric_key, info);
  @*/

///////////////////////////////////////////////////////////////////////////////
// Attacker proof obligations for this protocol ///////////////////////////////
///////////////////////////////////////////////////////////////////////////////

//@ ATTACKER_PROOFS_DEFAULT(rpc)

#endif