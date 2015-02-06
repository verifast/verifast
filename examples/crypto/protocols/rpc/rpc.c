#include "rpc.h"
#include "stdlib.h"

#define SERVER_PORT 121212

struct item *client(char server, struct item *key, struct item *request)
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
{
    struct network_status *net_stat = network_connect("localhost", SERVER_PORT);
    
    {
        struct item *tag = create_data_item_from_char(0);
        //@ item d = data_item(cons(0, nil));
        //@ assert item(tag, d, rpc_pub);
        //@ get_info_for_item(d);
        //@ close rpc_pub(d);
        //@ leak rpc_pub(d);
        struct item *payload = create_pair(tag, request);
        //@ item p = pair_item(d, req);
        //@ assert item(payload, p, rpc_pub);
        //@ get_info_for_item(p);
        //@ close rpc_pub(p);
        //@ leak rpc_pub(p);
        item_free(tag);
        struct item *hash = create_hmac(key, payload);
        //@ item h = hmac_item(creator, id, some(p));
        //@ if (!collision_in_run()) assert item(hash, h, rpc_pub);
        //@ get_info_for_item(h);
        //@ close rpc_pub(h);
        //@ leak rpc_pub(h);
        struct item *m = create_pair(hash, payload);
        //@ assert item(m, ?msg, rpc_pub);
        //@ item msg0 = pair_item(h, p);
        //@ if (!collision_in_run()) msg == msg0;
        //@ get_info_for_item(msg);
        //@ close rpc_pub(msg);
        //@ leak rpc_pub(msg);
        item_free(hash);
        item_free(payload);
        network_send(net_stat, m);
        item_free(m);
    }
    
    struct item *response;
    {
        struct item *r = network_receive(net_stat);
        check_is_pair(r);
        //@ assert item(r, pair_item(?h0, ?p0), rpc_pub);
        struct item *hash = pair_get_first(r);
        //@ assert item(hash, ?h, rpc_pub);
        struct item *payload = pair_get_second(r);
        //@ assert item(payload, ?p, rpc_pub);
        
        /*@ if (!collision_in_run())
            {
              assert h0 == h;
              assert p0 == p;
              open [_]rpc_pub(pair_item(h, p));
              open [_]rpc_pub(h);
              open [_]rpc_pub(p);
            }
        @*/
        item_free(r);
        hmac_verify(hash, key, payload);
        /*@ assert collision_in_run() ? 
                                true : h == hmac_item(creator, id, some(p)); @*/
        item_free(hash);
        struct item *tag = pair_get_first(payload);
        check_is_data(tag);
        char tagValue = item_get_data_as_char(tag);
        if (tagValue != 1) abort();
        //@ item d = data_item(cons(1, nil));
        //@ if (!collision_in_run()) assert item(tag, d, rpc_pub);
        item_free(tag);
        struct item *reqresp = pair_get_second(payload);
        struct item *request1 = pair_get_first(reqresp);
        response = pair_get_second(reqresp);
        //@ assert item(request1, ?req1, rpc_pub);
        //@ assert item(response, ?resp, rpc_pub);
        //@ if (!collision_in_run()) assert p == pair_item(d, pair_item(req1, resp));
        item_free(payload);
        item_free(reqresp);
        bool eq = item_equals(request, request1);
        if (!eq) abort();
        //@ assert collision_in_run() ? true : req1 == req;
        item_free(request1);
    }
    network_disconnect(net_stat);
    return response;
}

// This function represents the server application.
// We pass in the key predicate just to get hold of the creator principal id.
struct item *compute_response(int server, struct item *request)
  /*@ requires [?f]world(rpc_pub) &*&
               generated_values(server, ?count) &*&
               item(?key, symmetric_key_item(?creator, ?id), rpc_pub) &*&
               item(request, ?req, rpc_pub) &*&
               (
                 bad(creator) || 
                 bad(shared_with(creator, id)) || 
                 collision_in_run() ||
                 request(creator, shared_with(creator, id), req)
               );
  @*/
  /*@ ensures  [f]world(rpc_pub) &*& 
               generated_values(server, count + 1) &*&
               item(key, symmetric_key_item(creator, id), rpc_pub) &*& 
               item(request, req, rpc_pub) &*& 
               item(result, ?resp, rpc_pub) &*& [_]rpc_pub(resp) &*& 
               response(creator, shared_with(creator, id), req, resp) == true;
  @*/
{
  int random = random_int();
  struct item *response = create_data_item((void*) &random, (int) sizeof(int));
  //@ assert item(response, ?resp, rpc_pub);
  //@ assume (response(creator, shared_with(creator, id), req, resp) == true);
  //@ get_info_for_item(resp);
  //@ close rpc_pub(resp);
  //@ leak rpc_pub(resp);
  return response;
}

void server(char server, struct item *key)
  /*@ requires [?f0]world(rpc_pub) &*&
               generated_values(server, ?count) &*&
               item(key, symmetric_key_item(?creator, ?id), rpc_pub) &*&  
               shared_with(creator, id) == server;
  @*/
  /*@ ensures  [f0]world(rpc_pub) &*&
               generated_values(server, count + 1) &*&
               item(key, symmetric_key_item(creator, id), rpc_pub);
  @*/
{
    struct network_status *net_stat = network_bind_and_accept(SERVER_PORT);
    
    struct item *request = 0;
    {
        struct item *r = network_receive(net_stat);
        check_is_pair(r);
        //@ assert item(r, pair_item(?h0, ?p0), rpc_pub);
        struct item *hash = pair_get_first(r);
        //@ assert item(hash, ?h, rpc_pub);
        struct item *payload = pair_get_second(r);
        //@ assert item(payload, ?p, rpc_pub);
        
        /*@ if (!collision_in_run())
            {
              assert h0 == h;
              assert p0 == p;
              open [_]rpc_pub(pair_item(h, p));
              open [_]rpc_pub(h);
              open [_]rpc_pub(p);
            }
        @*/
        item_free(r);
        hmac_verify(hash, key, payload);
        /*@ if (!collision_in_run())
              assert h == hmac_item(creator, id, some(p)); @*/
        item_free(hash);
        struct item *tag = pair_get_first(payload);
        check_is_data(tag);
        char tagValue = item_get_data_as_char(tag);
        if (tagValue != 0) abort();
        //@ item d = data_item(cons(0, nil));
        request = pair_get_second(payload);
        
        /*@ if (!collision_in_run()) 
            {  
              assert item(tag, d, rpc_pub);
              assert item(request, ?req, rpc_pub);
              assert p == pair_item(d, req); 
            }
        @*/
        item_free(tag);
        item_free(payload);
    }
    
    //@ assert item(request, ?req, rpc_pub);
    struct item *response = compute_response(server, request);
    //@ assert item(response, ?resp, rpc_pub);
    
    {
        
        struct item *reqresp = create_pair(request, response);
        //@ item p = pair_item(req, resp);
        //@ assert item(reqresp, p, rpc_pub);
        //@ get_info_for_item(p);
        //@ close rpc_pub(p);
        //@ leak rpc_pub(p);
        item_free(response);
        item_free(request);
        struct item *tag = create_data_item_from_char(1);
        struct item *payload = create_pair(tag, reqresp);
        //@ item d = data_item(cons(1, nil));
        //@ get_info_for_item(d);
        //@ close rpc_pub(d);
        //@ leak rpc_pub(d);
        //@ assert item(payload, pair_item(d, p), rpc_pub);
        //@ get_info_for_item(pair_item(d, p));
        //@ close rpc_pub(pair_item(d, p));
        //@ leak rpc_pub(pair_item(d, p));
        item_free(tag);
        item_free(reqresp);
        struct item *hash = create_hmac(key, payload);
        //@ item h = hmac_item(creator, id, some(pair_item(d, p)));
        //@ if (!collision_in_run()) assert item(hash, h, rpc_pub);
        //@ get_info_for_item(h);
        //@ close rpc_pub(h);
        //@ leak rpc_pub(h);
        struct item *m = create_pair(hash, payload);
        //@ assert item(m, ?msg, rpc_pub);
        //@ if (!collision_in_run()) msg == pair_item(h, pair_item(d, p));
        //@ if (!collision_in_run()) assert item(m, msg, rpc_pub);
        //@ get_info_for_item(msg);
        //@ close rpc_pub(msg);
        //@ leak rpc_pub(msg);
        item_free(hash);
        item_free(payload);
        network_send(net_stat, m);
        item_free(m);
    }
    
    network_disconnect(net_stat);
}
