// See explanations in lib/dolevyao.h
#include "lib/dolevyao.h"
#include "stdlib.h"

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
// Configuration for this protocol ////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

/*@ 

lemma void create_principal();
  requires principals(?count);
  ensures principals(count + 1) &*& generated_keys(count, 0);

fixpoint int shared_with(int cl, int id);

@*/

/*
The example protocol uses two event predicates: "request(C, S, R)" states that 
client C sent a request item R to server S; "response(C, S, R, R1)" states that 
server S responded to request item R from client C with response item R1.
*/

/*@

fixpoint bool request(int cl, int sv, item req);
fixpoint bool response(int cl, int sv, item req, item resp);

@*/

///////////////////////////////////////////////////////////////////////////////
// Definition of pub for this protocol ////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

/*@

fixpoint bool mypub(item i) 
{
  switch (i) 
  {
    case key_item(p0, c0, k0, i0): return bad(p0) || bad(shared_with(p0, c0));
    case data_item(d0): return true;
    case hmac_item(creator0, count0, info0, m0): return
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
    case pair_item(first0, second0): return mypub(first0) && mypub(second0);
    default: return false;
  }
}

@*/

///////////////////////////////////////////////////////////////////////////////
// Protocol implementation ////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

struct item *client(int server, struct item *key, struct item *request)
  /*@ requires world(mypub) &*& 
               key_item(key, ?creator, ?id, symmetric_key, 0) &*& item(request, ?req) &*&
               mypub(req) == true &*& request(creator, server, req) == true &*& 
               shared_with(creator, id) == server; 
  @*/
  /*@ ensures  world(mypub) &*& 
               key_item(key, creator, id, symmetric_key, 0) &*& item(request, req) &*& 
               item(result, ?resp) &*& bad(creator) || bad(server) || 
               response(creator, server, req, resp) == true;  
  @*/
{
    {
        struct item *tag = create_data_item(0);
        struct item *payload = create_pair(tag, request);
        item_free(tag);
        struct item *hash = hmac(key, payload);
        struct item *m = create_pair(hash, payload);
        item_free(hash);
        item_free(payload);
        net_send(m);
        item_free(m);
    }
    
    {
        struct item *r = net_receive();
        struct item *hash = pair_get_first(r);
        struct item *payload = pair_get_second(r);
        item_free(r);
        hmacsha1_verify(hash, key, payload);
        item_free(hash);
        struct item *tag = pair_get_first(payload);
        int tagValue = item_get_data(tag);
        if (tagValue != 1) abort();
        item_free(tag);
        struct item *reqresp = pair_get_second(payload);
        item_free(payload);
        struct item *request1 = pair_get_first(reqresp);
        struct item *response = pair_get_second(reqresp);
        item_free(reqresp);
        bool eq = item_equals(request, request1);
        if (!eq) abort();
        item_free(request1);
        return response;
    }
}

// This function represents the server application.
// We pass in the key predicate just to get hold of the creator principal id.
struct item *compute_response(struct item *request);
  /*@ requires key_item(?key, ?creator, ?id, symmetric_key, ?info) &*& 
               item(request, ?req) &*& 
               bad(creator) || bad(shared_with(creator, id)) || 
               request(creator, shared_with(creator, id), req) == true; 
  @*/
  /*@ ensures  key_item(key, creator, id, symmetric_key, info) &*& 
               item(request, req) &*& 
               item(result, ?resp) &*& mypub(resp) == true &*& 
               response(creator, shared_with(creator, id), req, resp) == true;
  @*/

void server(int serverId, struct item *key)
  /*@ requires world(mypub) &*& key_item(key, ?creator, ?id, symmetric_key, ?info) &*& 
               shared_with(creator, id) == serverId; 
  @*/
  //@ ensures  false;
{
    for (;;)
        //@ invariant world(mypub) &*& key_item(key, creator, id, symmetric_key, info);
    {
        struct item *request = 0;
        {
            struct item *r = net_receive();
            struct item *hash = pair_get_first(r);
            struct item *payload = pair_get_second(r);
            item_free(r);
            hmacsha1_verify(hash, key, payload);
            item_free(hash);
            struct item *tag = pair_get_first(payload);
            int tagValue = item_get_data(tag);
            if (tagValue != 0) abort();
            item_free(tag);
            request = pair_get_second(payload);
            item_free(payload);
        }
        
        {
            struct item *response = compute_response(request);
            struct item *reqresp = create_pair(request, response);
            item_free(response);
            item_free(request);
            struct item *tag = create_data_item(1);
            struct item *payload = create_pair(tag, reqresp);
            item_free(tag);
            item_free(reqresp);
            struct item *hash = hmac(key, payload);
            struct item *m = create_pair(hash, payload);
            item_free(hash);
            item_free(payload);
            net_send(m);
            item_free(m);
        }
    }
}

///////////////////////////////////////////////////////////////////////////////
// Attacker representation ////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////// 

void attacker()
  //@ requires world(mypub) &*& principals(0);
  //@ ensures false;
{
    for (;;)
        //@ invariant world(mypub) &*& principals(?principalCount);
    {
        //@ create_principal(); // Attackers are arbitrary principals.
        for (;;)
            /*@ invariant world(mypub) &*& principals(_) &*& 
                          generated_keys(?me, ?keyCount); @*/
        {
            int action = choose();
            switch (action) {
                case 0:
                    // Bad principals leak keys...
                    //@ close key_request(me, 0);
                    struct item *item = create_key();
                    //@ open key_item(item, ?creator, ?id, symmetric_key, ?info);
                    //@ assume(bad(creator) || bad(shared_with(creator, id)));
                    net_send(item);
                    item_free(item);
                    break;
                case 1:
                    // Anyone can publish arbitrary data items...
                    int data = choose();
                    struct item *item = create_data_item(data);
                    net_send(item);
                    item_free(item);
                    break;
                case 2:
                    // Anyone can create pairs of public items...
                    struct item *first = net_receive();
                    struct item *second = net_receive();
                    struct item *pair = create_pair(first, second);
                    item_free(first);
                    item_free(second);
                    net_send(pair);
                    item_free(pair);
                    break;
                case 3:
                    // Anyone can hash a public item with a published key...
                    struct item *key = net_receive();
                    struct item *payload = net_receive();
                    check_is_key(key);
                    struct item *hash = hmac(key, payload);
                    //@ open key_item(key, _, _, _, _);
                    item_free(key);
                    item_free(payload);
                    net_send(hash);
                    item_free(hash);
                    break;
                case 4:
                    // Anyone can deconstruct a public pair...
                    struct item *pair = net_receive();
                    struct item *first = pair_get_first(pair);
                    struct item *second = pair_get_second(pair);
                    item_free(pair);
                    net_send(first);
                    item_free(first);
                    net_send(second);
                    item_free(second);
                    break;
            }
        }
        //@ leak principal(_, _);
    }
}