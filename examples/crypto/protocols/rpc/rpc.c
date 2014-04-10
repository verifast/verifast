#include "rpc.h"
#include "stdlib.h"

#define SERVER_PORT 121212

/*@ 
predicate protocol_pub(; fixpoint(item, bool) pub) = pub == rpc_pub;

lemma void init_protocol()
     requires true;
     ensures protocol_pub(rpc_pub);
{
  close protocol_pub(rpc_pub);
}
@*/

struct item *client(int server, struct item *key, struct item *request)
  /*@ requires [?f0]world(rpc_pub) &*&
               key_item(key, ?creator, ?id, symmetric_key, int_pair(0, 0)) &*& 
               item(request, ?req) &*&
               rpc_pub(req) == true &*& request(creator, server, req) == true &*& 
               shared_with(creator, id) == server; 
  @*/
  /*@ ensures  [f0]world(rpc_pub) &*&
               key_item(key, creator, id, symmetric_key, int_pair(0, 0)) &*& 
               item(request, req) &*& 
               item(result, ?resp) &*& bad(creator) || bad(server) || 
               response(creator, server, req, resp) == true;  
  @*/
{
    struct network_status *net_stat = network_connect("localhost", SERVER_PORT);
    
    {
        struct item *tag = create_data_item(0);
        struct item *payload = create_pair(tag, request);
        item_free(tag);
        struct item *hash = hmac(key, payload);
        struct item *m = create_pair(hash, payload);
        item_free(hash);
        item_free(payload);
        network_send(net_stat, m);
        item_free(m);
    }
    
    struct item *response;
    {
        struct item *r = network_receive(net_stat);
        struct item *hash = pair_get_first(r);
        struct item *payload = pair_get_second(r);
        item_free(r);
        hmac_verify(hash, key, payload);
        item_free(hash);
        struct item *tag = pair_get_first(payload);
        int tagValue = item_get_data(tag);
        if (tagValue != 1) abort();
        item_free(tag);
        struct item *reqresp = pair_get_second(payload);
        item_free(payload);
        struct item *request1 = pair_get_first(reqresp);
        response = pair_get_second(reqresp);
        item_free(reqresp);
        bool eq = item_equals(request, request1);
        if (!eq) abort();
        item_free(request1);
    }
    
    network_disconnect(net_stat);
    return response;
}

// This function represents the server application.
// We pass in the key predicate just to get hold of the creator principal id.
struct item *compute_response(struct item *request)
  /*@ requires [?f]world(rpc_pub) &*& 
               key_item(?key, ?creator, ?id, symmetric_key, ?info) &*& 
               item(request, ?req) &*& 
               bad(creator) || bad(shared_with(creator, id)) || 
               request(creator, shared_with(creator, id), req) == true; 
  @*/
  /*@ ensures  [f]world(rpc_pub) &*& 
               key_item(key, creator, id, symmetric_key, info) &*& 
               item(request, req) &*& 
               item(result, ?resp) &*& rpc_pub(resp) == true &*& 
               response(creator, shared_with(creator, id), req, resp) == true;
  @*/
{
  int random = choose();
  struct item *response = create_data_item(random);
  //@ assert item(response, ?resp);
  //@ assume (response(creator, shared_with(creator, id), req, resp) == true);
  return response;
}

void server(int serverId, struct item *key)
  /*@ requires [?f0]world(rpc_pub) &*&
               key_item(key, ?creator, ?id, symmetric_key, ?info) &*& 
               shared_with(creator, id) == serverId; 
  @*/
  /*@ ensures  [f0]world(rpc_pub) &*&
               key_item(key, creator, id, symmetric_key, info);
  @*/
{
    struct network_status *net_stat = network_bind(SERVER_PORT);
    
    struct item *request = 0;
    {
        struct item *r = network_receive(net_stat);
        struct item *hash = pair_get_first(r);
        struct item *payload = pair_get_second(r);
        item_free(r);
        hmac_verify(hash, key, payload);
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
        network_send(net_stat, m);
        item_free(m);
    }
    
    network_disconnect(net_stat);
}
