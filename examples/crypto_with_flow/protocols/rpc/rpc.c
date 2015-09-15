#include "rpc.h"

#include <stdlib.h>
#include <string.h>

//@ #include "quantifiers.gh"

#define SERVER_PORT 121212

void client(char *key, int key_len, char *request, char *response)
  /*@ requires [_]public_invar(rpc_pub) &*&
               principal(?client, _) &*&
               [?f1]cryptogram(key, key_len, ?key_cs, ?key_cg) &*&
                 key_cg == cg_symmetric_key(?creator, ?id) &*&
               [?f2]chars(request, PACKAGE_SIZE, ?req_cs) &*&
                 bad(creator) || 
                 request(creator, shared_with(creator, id), req_cs) == true &*&
               chars(response, PACKAGE_SIZE, _); @*/
  /*@ ensures  principal(client, _) &*&
               [f1]cryptogram(key, key_len, key_cs, key_cg) &*&
               [f2]chars(request, PACKAGE_SIZE, req_cs) &*&
               chars(response, PACKAGE_SIZE, ?resp_cs) &*&
                 collision_in_run || bad(creator) || 
                 bad(shared_with(creator, id)) ||
                 response(creator, shared_with(creator, id), 
                          req_cs, resp_cs); @*/
{
  int socket;
  char hmac[64];
  
  net_usleep(20000);
  if(net_connect(&socket, NULL, SERVER_PORT) != 0)
    abort();
  if(net_set_block(socket) != 0)
    abort();
  
  {
    int message_len = 1 + PACKAGE_SIZE + 64;
    char* message = malloc(message_len);
    if (message == 0) abort();
    
    *message = '0';
    //@ close [f2]optional_crypto_chars(false, request, PACKAGE_SIZE, req_cs);
    memcpy(message + 1, request, PACKAGE_SIZE);
    //@ open [f2]optional_crypto_chars(false, request, PACKAGE_SIZE, req_cs);
    //@ list<char> t_req_cs = cons('0', req_cs);
    //@ assert chars(message, PACKAGE_SIZE + 1, t_req_cs);
    //@ close optional_crypto_chars(false, message, PACKAGE_SIZE + 1, t_req_cs);
    sha512_hmac(key, (unsigned int) key_len, message, 
                (unsigned int) PACKAGE_SIZE + 1, hmac, 0);
    //@ open optional_crypto_chars(false, message, PACKAGE_SIZE + 1, t_req_cs);
    //@ assert cryptogram(hmac, 64, ?hmac_cs, ?hmac_cg);
    //@ close rpc_pub(hmac_cg);
    //@ leak rpc_pub(hmac_cg);
    //@ public_cryptogram(hmac, hmac_cg);
    //@ close optional_crypto_chars(false, hmac, 64, hmac_cs);
    memcpy(message + PACKAGE_SIZE + 1, hmac, 64);
    //@ open optional_crypto_chars(false, hmac, 64, hmac_cs);
    //@ open optional_crypto_chars(false, message + 1 + 40, 64, hmac_cs);
    //@ chars_join(message);
    net_send(&socket, message, (unsigned int) message_len);
    free(message);
  }
  
  {
    int size;
    char request2[PACKAGE_SIZE];
    char buffer[MAX_MESSAGE_SIZE];
    size = net_recv(&socket, buffer, MAX_MESSAGE_SIZE);
    int expected_size = 1 + 2 * PACKAGE_SIZE + 64;
    if (size != expected_size) abort();
    //@ chars_split(buffer, expected_size);
    /*@ close hide_chars((void*) buffer + expected_size, 
                         MAX_MESSAGE_SIZE - expected_size, _); @*/
    
    //Verify the hmac
    /*@ close optional_crypto_chars(false, buffer, 
                                    1 + 2 * PACKAGE_SIZE, ?cont_cs); @*/
    sha512_hmac(key, (unsigned int) key_len, buffer, 
                (unsigned int) (1 + 2 * PACKAGE_SIZE), hmac, 0);
    /*@ open optional_crypto_chars(false, buffer, 
                                   1 + 2 * PACKAGE_SIZE, cont_cs); @*/
    //@ open cryptogram(hmac, 64, ?hmac_cs, ?hmac_cg);
    //@ assert hmac_cg == cg_hmac(creator, id, cont_cs);
    //@ close optional_crypto_chars(!collision_in_run, hmac, 64, hmac_cs);
    /*@ close optional_crypto_chars(false, 
                              (void*) buffer + 1 + 2 * PACKAGE_SIZE, 64, _); @*/
    if (memcmp((void*) buffer + 1 + 2 * PACKAGE_SIZE, hmac, 64) != 0) abort();
    //@ open optional_crypto_chars(!collision_in_run, hmac, 64, hmac_cs);
    //@ assert chars((void*) buffer + 1 + 2 * PACKAGE_SIZE, 64, hmac_cs);
    //@ public_chars((void*) buffer + 1 + 2 * PACKAGE_SIZE, 64, hmac_cs);
    //@ assert chars(buffer, expected_size, append(cont_cs, hmac_cs));
    
    //Check the message tag hmac
    //@ chars_split(buffer, 1);
    if (buffer[0] != '1') abort();
    //Check if response is for the correct request
    //@ chars_split((void*) buffer + 1, PACKAGE_SIZE);
    /*@ close optional_crypto_chars(false, (void*) buffer + 1, 
                                    PACKAGE_SIZE, ?req_cs2); @*/
    //@ close [f2]optional_crypto_chars(false, request, PACKAGE_SIZE, _);
    if (memcmp(request, (void*) buffer + 1, PACKAGE_SIZE) != 0) abort();
    /*@ open optional_crypto_chars(false, (void*) buffer + 1, 
                                   PACKAGE_SIZE, req_cs2); @*/
    //@ open [f2]optional_crypto_chars(false, request, PACKAGE_SIZE, _);
    //@ assert req_cs == req_cs2;
    //Retrieve the actual response
    /*@ close optional_crypto_chars(false, (void*) buffer + 1 + PACKAGE_SIZE, 
                                    PACKAGE_SIZE, ?resp_cs); @*/
    memcpy(response, (void*) buffer + 1 + PACKAGE_SIZE, PACKAGE_SIZE);
    /*@ open optional_crypto_chars(false, (void*) buffer + 1 + PACKAGE_SIZE, 
                                   PACKAGE_SIZE, resp_cs); @*/
    //@ assert chars(response, PACKAGE_SIZE, resp_cs);
    
    /*@ if (!collision_in_run && !bad(creator) && 
            !bad(shared_with(creator, id)))
        {
          switch (cont_cs) 
          {
            case cons(c1, cs1):
              if (c1 == '1')
              {
                public_chars((void*) buffer + 1 + 2 * PACKAGE_SIZE, 
                             64, hmac_cs);
                close cryptogram(hmac, 64, hmac_cs, hmac_cg);
                public_cryptogram_extract(hmac);
                open [_]rpc_pub(hmac_cg);
              }
              else
              {
                assert false;
              }
            case nil:
              assert false;
          };

          assert true == 
                   response(creator, shared_with(creator, id), req_cs, resp_cs);
        }
    @*/
    
    /*@ open hide_chars((void*) buffer + expected_size,  
                        MAX_MESSAGE_SIZE - expected_size, _); @*/
    //@ chars_join((void*) buffer + 1);
    //@ chars_join(buffer);
    //@ chars_join(buffer);
    //@ chars_join(buffer);
    //@ assert chars(buffer, MAX_MESSAGE_SIZE, _);
    //@ if (!collision_in_run) public_crypto_chars(hmac, 64, hmac_cs);
  }
  net_close(socket);
}

// This function represents the server application.
// We pass the key predicate just to get hold of the creator principal id.
void compute_response(char* request, char* response)
  /*@ requires [_]public_invar(rpc_pub) &*&
               principal(?server, ?count) &*&
               [?f1]cryptogram(?key, ?key_len, ?key_cs, ?key_cg) &*&
                 key_cg == cg_symmetric_key(?client, ?id) &*&
               [?f2]chars(request, PACKAGE_SIZE, ?req_cs) &*&
               chars(response, PACKAGE_SIZE, _) &*&
               (
                 collision_in_run || bad(client) || bad(server) ||
                 request(client, server, req_cs)
               ); @*/
  /*@ ensures  principal(server, count + 1) &*&
               [f1]cryptogram(key, key_len, key_cs, key_cg) &*&
               [f2]chars(request, PACKAGE_SIZE, req_cs) &*&
               chars(response, PACKAGE_SIZE, ?resp_cs) &*&
               true == response(client, server, req_cs, resp_cs); @*/
{
  havege_state havege_state;
  //@ close havege_state(&havege_state);
  havege_init(&havege_state);
  
  //@ close random_request(server, 0, false);
  if (havege_random(&havege_state, response, PACKAGE_SIZE) != 0) abort();
  
  //@ assert cryptogram(response, PACKAGE_SIZE, ?resp_cs, ?resp_cg);
  //@ close rpc_pub(resp_cg);
  //@ leak rpc_pub(resp_cg);
  //@ public_cryptogram(response, resp_cg);
  //@ assume (response(client, server, req_cs, resp_cs));
  
  havege_free(&havege_state);
  //@ open havege_state(&havege_state);
}

void server(char *key, int key_len, char *request, char *response)
  /*@ requires [_]public_invar(rpc_pub) &*&
               principal(?server, _) &*&
               [?f1]cryptogram(key, key_len, ?key_cs, ?key_cg) &*&
                 key_cg == cg_symmetric_key(?client, ?id) &*&
                 server == shared_with(client, id) &*&
               chars(request, PACKAGE_SIZE, _) &*&
               chars(response, PACKAGE_SIZE, _); @*/
  /*@ ensures  principal(server, _) &*&
               [f1]cryptogram(key, key_len, key_cs, key_cg) &*&
               chars(request, PACKAGE_SIZE, ?req_cs) &*&
                 collision_in_run || bad(client) || 
                 request(client, server, req_cs) &*&
               chars(response, PACKAGE_SIZE, ?resp_cs) &*&
                 collision_in_run ||
                 bad(client) || bad(server) ||
                 response(client, server, req_cs, resp_cs); @*/
{
  int socket1;
  int socket2;
  
  if(net_bind(&socket1, NULL, SERVER_PORT) != 0)
    abort();
  if(net_accept(socket1, &socket2, NULL) != 0)
    abort();
  if(net_set_block(socket2) != 0)
    abort();
  
  {
    int size;
    char buffer[MAX_MESSAGE_SIZE];
    char hmac[64];
  
    size = net_recv(&socket2, buffer, MAX_MESSAGE_SIZE);
    int expected_size = 1 + PACKAGE_SIZE + 64;
    if (size != expected_size) abort();
    //@ chars_split(buffer, expected_size);
    /*@ close hide_chars((void*) buffer + expected_size, 
                         MAX_MESSAGE_SIZE - expected_size, _); @*/
    
    //Verify the hmac
    //@ close optional_crypto_chars(false, buffer, 1 + PACKAGE_SIZE, ?cont_cs);
    sha512_hmac(key, (unsigned int) key_len, buffer, 
                (unsigned int) (1 + PACKAGE_SIZE), hmac, 0);
    //@ open optional_crypto_chars(false, buffer, 1 + PACKAGE_SIZE, cont_cs);
    //@ open cryptogram(hmac, 64, ?hmac_cs, ?hmac_cg);
    //@ assert hmac_cg == cg_hmac(client, id, cont_cs);
    //@ close optional_crypto_chars(!collision_in_run, hmac, 64, hmac_cs);
    /*@ close optional_crypto_chars(false, (void*) buffer + 1 + PACKAGE_SIZE,
                                    64, _); @*/
    if (memcmp((void*) buffer + 1 + PACKAGE_SIZE, hmac, 64) != 0) abort();
    //@ open optional_crypto_chars(!collision_in_run, hmac, 64, hmac_cs);
    /*@ open optional_crypto_chars(false, (void*) buffer + 1 + PACKAGE_SIZE, 
                                   64, hmac_cs); @*/
    //@ assert chars((void*) buffer + 1 + PACKAGE_SIZE, 64, hmac_cs);
    //@ public_chars((void*) buffer + 1 + PACKAGE_SIZE, 64, hmac_cs);    
    //@ assert chars(buffer, expected_size, append(cont_cs, hmac_cs));
    
    //Check the message tag hmac
    //@ chars_split(buffer, 1);
    if (buffer[0] != '0') abort();
    //Retrieve the actual request
    /*@ close optional_crypto_chars(false, (void*) buffer + 1, 
                                    PACKAGE_SIZE, ?req_cs); @*/
    memcpy(request, (void*) buffer + 1, PACKAGE_SIZE);
    /*@ open optional_crypto_chars(false, (void*) buffer + 1, 
                                   PACKAGE_SIZE, req_cs); @*/
    //@ assert chars(request, PACKAGE_SIZE, req_cs);
    
    /*@ switch (cont_cs) 
        {
          case cons(c1, cs1):
            assert cont_cs == cons('0', req_cs);
            if (!collision_in_run && c1 == '0' && !bad(client))
            {
              public_chars((void*) buffer + 1 + PACKAGE_SIZE, 64, hmac_cs);
              close cryptogram(hmac, 64, hmac_cs, hmac_cg);
              public_cryptogram_extract(hmac);
              open [_]rpc_pub(hmac_cg);
              assert (true == request(client, server, req_cs));
            }
          case nil:
            assert false;
        }
    @*/
    
    //@ chars_join((void*) buffer + 1);
    //@ chars_join(buffer);
    /*@ open hide_chars((void*) buffer + expected_size, 
                        MAX_MESSAGE_SIZE - expected_size, _); @*/
    //@ if (!collision_in_run) public_crypto_chars(hmac, 64, hmac_cs);
  }
  
  //@ assert chars(request, PACKAGE_SIZE, ?req_cs);
  compute_response(request, response);
  //@ assert chars(response, PACKAGE_SIZE, ?resp_cs);
  
  {
    char hmac[64];
  
    int message_len = 1 + 2 * PACKAGE_SIZE + 64;
    char* message = malloc(message_len);
    if (message == 0) abort();
    //@ chars_split(message, 1 + 2 * PACKAGE_SIZE);
    
    //@ chars_split(message, 1);
    *message = '1';
    //@ open chars(message + 1, 0, _);
    //@ chars_split(message + 1, PACKAGE_SIZE);
    //@ close optional_crypto_chars(false, request, PACKAGE_SIZE, req_cs);
    memcpy(message + 1, request, PACKAGE_SIZE);
    //@ open optional_crypto_chars(false, message + 1, PACKAGE_SIZE, req_cs);
    //@ open optional_crypto_chars(false, request, PACKAGE_SIZE, req_cs);
    //@ close optional_crypto_chars(false, response, PACKAGE_SIZE, resp_cs);
    memcpy(message + 1 + PACKAGE_SIZE, response, PACKAGE_SIZE);
    /*@ open optional_crypto_chars(false, message + 1 + PACKAGE_SIZE, 
                                   PACKAGE_SIZE, resp_cs); @*/
    //@ open optional_crypto_chars(false, response, PACKAGE_SIZE, resp_cs);
    //@ chars_join(message + 1);
    //@ assert chars(message, message_len, _);
    
    //@ list<char> pay = cons('1', append(req_cs, resp_cs));
    //@ close optional_crypto_chars(false, message, 1 + 2 * PACKAGE_SIZE, pay);
    sha512_hmac(key, (unsigned int) key_len, message, 
                (unsigned int) 2 * PACKAGE_SIZE + 1, hmac, 0);
    //@ open optional_crypto_chars(false, message, 1 + 2 * PACKAGE_SIZE, pay);
    //@ open cryptogram(hmac, 64, ?hmac_cs, ?hmac_cg);
    //@ assert hmac_cg == cg_hmac(client, id, pay);
    //@ close optional_crypto_chars(!collision_in_run, hmac, 64, hmac_cs);
    memcpy(message + 1 + 2 * PACKAGE_SIZE, hmac, 64);
    //@ open optional_crypto_chars(!collision_in_run, hmac, 64, hmac_cs);
    /*@ open optional_crypto_chars(!collision_in_run, 
                               message + 1 + 2 * PACKAGE_SIZE, 64, hmac_cs); @*/
    //@ close cryptogram(message + 1 + 2 * PACKAGE_SIZE, 64, hmac_cs, hmac_cg);
    //@ drop_append(PACKAGE_SIZE, req_cs, resp_cs);
    //@ take_append(PACKAGE_SIZE, req_cs, resp_cs);
    //@ close rpc_pub(hmac_cg);    
    //@ leak rpc_pub(hmac_cg);
    //@ public_cryptogram(message + 1 + 2 * PACKAGE_SIZE, hmac_cg);
    //@ assert chars(message, message_len, _);
    
    net_send(&socket2, message, (unsigned int) message_len);
    //@ close optional_crypto_chars(false, message, message_len, _);
    free((void*) message);
    //@ close cryptogram(hmac, 64, hmac_cs, hmac_cg);
    //@ public_cryptogram(hmac, hmac_cg);
  }
  
  net_close(socket2);
  net_close(socket1);
}