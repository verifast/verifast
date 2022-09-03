#include "rpc.h"
#include "stdlib.h"

#define SERVER_PORT 121212

struct item *client(char server, struct item *key, struct item *request)
  /*@ requires [?f0]world(rpc_pub, rpc_key_clsfy) &*& 
               principal(?client, ?count) &*&
               item(key, symmetric_key_item(?creator, ?id), rpc_pub) &*&
               item(request, ?req, rpc_pub) &*& [_]rpc_pub(req) &*&
               true == request(creator, server, req) &*&
               shared_with(creator, id) == server;
  @*/
  /*@ ensures  [f0]world(rpc_pub, rpc_key_clsfy) &*& 
               principal(client, count) &*&
               item(key, symmetric_key_item(creator, id), rpc_pub) &*&
               item(request, req, rpc_pub) &*& item(result, ?resp, rpc_pub) &*& 
               (
                 col || bad(creator) || bad(server) ||
                 response(creator, server, req, resp)
               );
  @*/
{
    struct network_status *net_stat = network_connect("localhost", SERVER_PORT);
    
    {
        struct item *tag = create_data_item_from_int(0);
        //@ item d = data_item(chars_of_int(0));
        //@ assert item(tag, d, rpc_pub);
        //@ close rpc_pub(d);
        //@ leak rpc_pub(d);
        struct item *payload = create_pair(tag, request);
        //@ item p = pair_item(d, req);
        //@ assert item(payload, p, rpc_pub);
        //@ close rpc_pub(p);
        //@ leak rpc_pub(p);
        item_free(tag);
        struct item *hash = create_hmac(key, payload);
        //@ item h = hmac_item(creator, id, some(p));
        //@ if (!col) assert item(hash, h, rpc_pub);
        //@ close rpc_pub(h);
        //@ leak rpc_pub(h);
        struct item *m = create_pair(hash, payload);
        //@ assert item(m, ?msg, rpc_pub);
        //@ item msg0 = pair_item(h, p);
        //@ if (!col) msg == msg0;
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
        struct item *hmac1 = pair_get_first(r);
        //@ assert item(hmac1, ?h, rpc_pub);
        struct item *payload = pair_get_second(r);
        //@ assert item(payload, ?p, rpc_pub);
        
        /*@ if (!col)
            {
              assert h0 == h;
              assert p0 == p;
              open [_]rpc_pub(pair_item(h, p));
              open [_]rpc_pub(h);
              open [_]rpc_pub(p);
            }
            else
            {
              close rpc_pub(p);
              leak rpc_pub(p);
            }
        @*/
        struct item *hmac2 = create_hmac(key, payload);
        item_check_equal(hmac1, hmac2);
        item_free(hmac1);
        item_free(hmac2);
        item_free(r);
        //@ assert col || h == hmac_item(creator, id, some(p));
       
        struct item *tag = pair_get_first(payload);
        check_is_data(tag);
        int tagValue = item_get_data_as_int(tag);
        if (tagValue != 1) abort();
        //@ item d = data_item(chars_of_int(1));
        //@ assert item(tag, ?d0, rpc_pub);
        //@ assert col || d == d0;
        item_free(tag);
        struct item *reqresp = pair_get_second(payload);
        struct item *request1 = pair_get_first(reqresp);
        response = pair_get_second(reqresp);
        //@ assert item(request1, ?req1, rpc_pub);
        //@ assert item(response, ?resp, rpc_pub);
        //@ if (!col) assert p == pair_item(d, pair_item(req1, resp));
        item_free(payload);
        item_free(reqresp);
        item_check_equal(request, request1);
        //@ assert col || req1 == req;
        item_free(request1);
    }
    network_disconnect(net_stat);
    return response;
}

// This function represents the server application.
// We pass in the key predicate just to get hold of the creator principal id.
struct item *compute_response(int server, struct item *request)
  /*@ requires [?f]world(rpc_pub, rpc_key_clsfy) &*&
               principal(server, ?count) &*&
               item(?key, symmetric_key_item(?creator, ?id), rpc_pub) &*&
               item(request, ?req, rpc_pub) &*&
               (
                 col || bad(creator) || bad(shared_with(creator, id)) ||
                 request(creator, shared_with(creator, id), req)
               );
  @*/
  /*@ ensures  [f]world(rpc_pub, rpc_key_clsfy) &*& 
               principal(server, count + 1) &*&
               item(key, symmetric_key_item(creator, id), rpc_pub) &*& 
               item(request, req, rpc_pub) &*& 
               item(result, ?resp, rpc_pub) &*& [_]rpc_pub(resp) &*& 
               response(creator, shared_with(creator, id), req, resp) == true;
  @*/
{
  //@ item n = nonce_item(server, count + 1, 0);
  //@ close rpc_pub(n);  
  //@ leak rpc_pub(n);
  int random = random_int();
  struct item *response = create_data_item((void*) &random, (int) sizeof(int));
  //@ assert item(response, ?resp, rpc_pub);
  //@ assume (response(creator, shared_with(creator, id), req, resp) == true);
  //@ close rpc_pub(resp);
  //@ leak rpc_pub(resp);
  return response;
  //@ chars_to_integer(&random);
}

void server(char server, struct item *key)
  /*@ requires [?f0]world(rpc_pub, rpc_key_clsfy) &*&
               principal(server, ?count) &*&
               item(key, symmetric_key_item(?creator, ?id), rpc_pub) &*&  
               shared_with(creator, id) == server;
  @*/
  /*@ ensures  [f0]world(rpc_pub, rpc_key_clsfy) &*&
               principal(server, count + 1) &*&
               item(key, symmetric_key_item(creator, id), rpc_pub);
  @*/
{
    struct network_status *net_stat = network_bind_and_accept(SERVER_PORT);
    
    struct item *request = 0;
    {
        struct item *r = network_receive(net_stat);
        check_is_pair(r);
        //@ assert item(r, pair_item(?h0, ?p0), rpc_pub);
        struct item *hmac1 = pair_get_first(r);
        //@ assert item(hmac1, ?h, rpc_pub);
        struct item *payload = pair_get_second(r);
        //@ assert item(payload, ?p, rpc_pub);
        
        /*@ if (!col)
            {
              assert h0 == h;
              assert p0 == p;
              open [_]rpc_pub(pair_item(h, p));
              open [_]rpc_pub(h);
              open [_]rpc_pub(p);
            }
            else
            {
              close rpc_pub(p);
              leak rpc_pub(p);
            }
        @*/
        struct item *hmac2 = create_hmac(key, payload);
        item_check_equal(hmac1, hmac2);
        item_free(hmac1);
        item_free(hmac2);
        item_free(r);
        //@ assert col || h == hmac_item(creator, id, some(p));
        struct item *tag = pair_get_first(payload);
        check_is_data(tag);
        int tagValue = item_get_data_as_int(tag);
        if (tagValue != 0) abort();
        //@ item d = data_item(chars_of_int(0));
        request = pair_get_second(payload);
        
        /*@ if (!col) 
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
        //@ close rpc_pub(p);
        //@ leak rpc_pub(p);
        item_free(response);
        item_free(request);
        struct item *tag = create_data_item_from_int(1);
        struct item *payload = create_pair(tag, reqresp);
        //@ item d = data_item(chars_of_int(1));
        //@ close rpc_pub(d);
        //@ leak rpc_pub(d);
        //@ assert item(payload, pair_item(d, p), rpc_pub);
        //@ close rpc_pub(pair_item(d, p));
        //@ leak rpc_pub(pair_item(d, p));
        item_free(tag);
        item_free(reqresp);
        struct item *hash = create_hmac(key, payload);
        //@ item h = hmac_item(creator, id, some(pair_item(d, p)));
        //@ if (!col) assert item(hash, h, rpc_pub);
        //@ close rpc_pub(h);
        //@ leak rpc_pub(h);
        struct item *m = create_pair(hash, payload);
        //@ assert item(m, ?msg, rpc_pub);
        //@ if (!col) msg == pair_item(h, pair_item(d, p));
        //@ if (!col) assert item(m, msg, rpc_pub);
        //@ close rpc_pub(msg);
        //@ leak rpc_pub(msg);
        item_free(hash);
        item_free(payload);
        network_send(net_stat, m);
        item_free(m);
    }
    
    network_disconnect(net_stat);
}
