#include "rpc.h"

#include <stdlib.h>
#include <string.h>

//@ #include "quantifiers.gh"

#define SERVER_PORT 121212

void client(char *key, int key_len, char *request, char *response)
  /*@ requires [_]public_invar(rpc_pub) &*&
               principal(?client, _) &*&
               [?f1]cryptogram(key, key_len, ?key_ccs, ?key_cg) &*&
                 key_cg == cg_symmetric_key(?creator, ?id) &*&
               [?f2]chars(request, PACKAGE_SIZE, ?req_cs) &*&
                 bad(creator) ||
                 request(creator, shared_with(creator, id), req_cs) == true &*&
               chars_(response, PACKAGE_SIZE, _); @*/
  /*@ ensures  principal(client, _) &*&
               [f1]cryptogram(key, key_len, key_ccs, key_cg) &*&
               [f2]chars(request, PACKAGE_SIZE, req_cs) &*&
               chars(response, PACKAGE_SIZE, ?resp_cs) &*&
                 col || bad(creator) || bad(shared_with(creator, id)) ||
                 response(creator, shared_with(creator, id),
                          req_cs, resp_cs); @*/
{
  //@ open principal(client, _);
  int socket;
  char hmac[64];

  net_usleep(20000);
  if(net_connect(&socket, NULL, SERVER_PORT) != 0)
    abort();
  if(net_set_block(socket) != 0)
    abort();

  {
    size_t message_len = 1U + PACKAGE_SIZE + 64U;
    char* message = malloc(message_len);
    if (message == 0) abort();

    *message = '0';
    //@ chars_to_crypto_chars(request, PACKAGE_SIZE);
    crypto_memcpy(message + 1, request, PACKAGE_SIZE);
    //@ list<char> t_req_cs = cons('0', req_cs);
    //@ cs_to_ccs_crypto_chars(request, req_cs);
    //@ cs_to_ccs_crypto_chars(message + 1, req_cs);
    //@ assert chars(message, PACKAGE_SIZE + 1, t_req_cs);
    //@ chars_to_crypto_chars(message, PACKAGE_SIZE + 1);
    //@ MEMCMP_PUB(message)
    sha512_hmac(key, (unsigned int) key_len, message,
                (unsigned int) PACKAGE_SIZE + 1, hmac, 0);
    //@ assert cryptogram(hmac, 64, ?hmac_ccs, ?hmac_cg);
    //@ close exists(t_req_cs);
    //@ close rpc_pub(hmac_cg);
    //@ leak rpc_pub(hmac_cg);
    //@ public_cryptogram(hmac, hmac_cg);
    //@ assert chars(hmac, 64, ?hmac_cs);
    //@ chars_to_crypto_chars(hmac, 64);
    crypto_memcpy(message + PACKAGE_SIZE + 1, hmac, 64);
    //@ cs_to_ccs_crypto_chars(hmac, hmac_cs);
    //@ cs_to_ccs_crypto_chars(message + 1 + PACKAGE_SIZE, hmac_cs);
    //@ cs_to_ccs_crypto_chars(message, t_req_cs);
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

    //Verify the hmac
    //@ assert chars(buffer, 1 + 2 * PACKAGE_SIZE, ?cont_cs);
    //@ chars_to_crypto_chars(buffer, 1 + 2 * PACKAGE_SIZE);
    //@ MEMCMP_PUB(buffer)
    //@ chars_to_chars_(hmac);
    sha512_hmac(key, (unsigned int) key_len, buffer,
                (unsigned int) (1 + 2 * PACKAGE_SIZE), hmac, 0);
    //@ open cryptogram(hmac, 64, ?hmac_ccs, ?hmac_cg);
    //@ assert hmac_cg == cg_sha512_hmac(creator, id, ?cont_ccs);
    //@ cs_to_ccs_crypto_chars(buffer, cont_cs);

    //@ chars_split((void*) buffer + 1 + 2 * PACKAGE_SIZE, 64);
    //@ assert [1/2]chars((void*) buffer + 1 + 2 * PACKAGE_SIZE, 64, ?hmac_cs);
    //@ public_chars((void*) buffer + 1 + 2 * PACKAGE_SIZE, 64);
    //@ chars_to_crypto_chars((void*) buffer + 1 + 2 * PACKAGE_SIZE, 64);
    //@ MEMCMP_SEC(hmac, hmac_cg)
    //@ MEMCMP_PUB((void*) buffer + 1 + 2 * PACKAGE_SIZE)
    if (crypto_memcmp((void*) buffer + 1 + 2 * PACKAGE_SIZE, hmac, 64) != 0) abort();
    //@ cs_to_ccs_crypto_chars((void*) buffer + 1 + 2 * PACKAGE_SIZE, hmac_cs);
    //@ public_crypto_chars(hmac, 64);
    //@ chars_split(buffer, 1 + 2 * PACKAGE_SIZE);
    //@ close [1/2]hide_chars(buffer, 1 + 2 * PACKAGE_SIZE, cont_cs);

    //Check the message tag hmac
    //@ chars_split(buffer, 1);
    if (buffer[0] != '1') abort();
    //@ close [1/2]chars(buffer, 1, cons('1', nil));

    //Check if response is for the correct request
    //@ chars_split((void*) buffer + 1, PACKAGE_SIZE);
    //@ assert [f2]chars(request, PACKAGE_SIZE, req_cs);
    //@ chars_to_crypto_chars(request, PACKAGE_SIZE);
    //@ chars_to_crypto_chars((void*) buffer + 1, PACKAGE_SIZE);
    //@ MEMCMP_PUB(request)
    //@ MEMCMP_PUB((void*) buffer + 1)
    if (crypto_memcmp(request, (void*) buffer + 1, PACKAGE_SIZE) != 0) abort();
    //@ cs_to_ccs_crypto_chars(request, req_cs);
    //@ cs_to_ccs_crypto_chars((void*) buffer + 1, req_cs);

    //Retrieve the actual response
    //@ assert [1/2]chars((void*) buffer + 1 + PACKAGE_SIZE, PACKAGE_SIZE, ?resp_cs);
    //@ chars_to_crypto_chars((void*) buffer + 1 + PACKAGE_SIZE, PACKAGE_SIZE);
    crypto_memcpy(response, (void*) buffer + 1 + PACKAGE_SIZE, PACKAGE_SIZE);
    //@ cs_to_ccs_crypto_chars(response, resp_cs);
    //@ cs_to_ccs_crypto_chars((void*) buffer + 1 + PACKAGE_SIZE, resp_cs);
    //@ chars_join(buffer);
    //@ chars_join(buffer);
    //@ open [1/2]hide_chars(buffer, 1 + 2 * PACKAGE_SIZE, cont_cs);
    //@ assert cont_cs == cons('1', append(req_cs, resp_cs));

    /*@ if (!col && !bad(creator) && !bad(shared_with(creator, id)))
        {
          switch (cont_cs)
          {
            case cons(c1, cs1):
              if (c1 == '1')
              {
                public_chars((void*) buffer + 1 + 2 * PACKAGE_SIZE, 64);
                public_ccs_cg(hmac_cg);
                open [_]rpc_pub(hmac_cg);
                assert [_]exists(?cont_cs');
                cs_to_ccs_inj(cont_cs, cont_cs');
                take_append(PACKAGE_SIZE, req_cs, resp_cs);
              }
              else
              {
                assert false;
              }
            case nil:
              assert false;
          };

          assert true == response(creator, shared_with(creator, id),
                                  req_cs, resp_cs);
        }
    @*/
    //@ chars_join(buffer);
    //@ chars_join(buffer);
  }
  net_close(socket);
  //@ close principal(client, _);
}

// This function represents the server application.
// We pass the key predicate just to get hold of the creator principal id.
void compute_response(char* request, char* response)
  /*@ requires [_]public_invar(rpc_pub) &*&
               principal(?server, ?count) &*&
               [?f1]cryptogram(?key, ?key_len, ?key_ccs, ?key_cg) &*&
                 key_cg == cg_symmetric_key(?client, ?id) &*&
               [?f2]chars(request, PACKAGE_SIZE, ?req_cs) &*&
               chars_(response, PACKAGE_SIZE, _) &*&
               (
                 col || bad(client) || bad(server) ||
                 request(client, server, req_cs)
               ); @*/
  /*@ ensures  principal(server, count + 1) &*&
               [f1]cryptogram(key, key_len, key_ccs, key_cg) &*&
               [f2]chars(request, PACKAGE_SIZE, req_cs) &*&
               chars(response, PACKAGE_SIZE, ?resp_cs) &*&
               true == response(client, server, req_cs, resp_cs); @*/
{
  //@ open principal(server, count);
  havege_state havege_state;
  //@ close havege_state(&havege_state);
  havege_init(&havege_state);

  //@ close random_request(server, 0, false);
  if (havege_random(&havege_state, response, PACKAGE_SIZE) != 0) abort();

  //@ assert cryptogram(response, PACKAGE_SIZE, ?resp_ccs, ?resp_cg);
  //@ close rpc_pub(resp_cg);
  //@ leak rpc_pub(resp_cg);
  //@ public_cryptogram(response, resp_cg);
  //@ assert chars(response, PACKAGE_SIZE, ?resp_cs);
  //@ assume (response(client, server, req_cs, resp_cs));

  havege_free(&havege_state);
  //@ open havege_state(&havege_state);
  //@ close principal(server, count + 1);
}

void server(char *key, int key_len, char *request, char *response)
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
{
  //@ open principal(server, _);
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

    //Verify the hmac
    //@ assert chars(buffer, 1 + PACKAGE_SIZE, ?cont_cs);
    //@ chars_to_crypto_chars(buffer, 1 + PACKAGE_SIZE);
    //@ MEMCMP_PUB(buffer)
    sha512_hmac(key, (unsigned int) key_len, buffer,
                (unsigned int) (1 + PACKAGE_SIZE), hmac, 0);
    //@ assert crypto_chars(normal, buffer, 1 + PACKAGE_SIZE, ?cont_ccs);
    //@ cs_to_ccs_crypto_chars(buffer, cont_cs);
    //@ open cryptogram(hmac, 64, ?hmac_ccs, ?hmac_cg);
    //@ assert hmac_cg == cg_sha512_hmac(client, id, cont_ccs);

    //@ public_chars((void*) buffer + 1 + PACKAGE_SIZE, 64);
    //@ assert chars((void*) buffer + 1 + PACKAGE_SIZE, 64, ?hmac_cs);
    //@ chars_to_crypto_chars((void*) buffer + 1 + PACKAGE_SIZE, 64);
    //@ MEMCMP_SEC(hmac, hmac_cg)
    //@ MEMCMP_PUB((void*) buffer + 1 + PACKAGE_SIZE)
    if (crypto_memcmp((void*) buffer + 1 + PACKAGE_SIZE, hmac, 64) != 0) abort();
    //@ public_crypto_chars(hmac, 64);
    //@ cs_to_ccs_chars(hmac, hmac_cs);
    //@ cs_to_ccs_crypto_chars((void*) buffer + 1 + PACKAGE_SIZE, hmac_cs);
    //@ chars_join(buffer);
    //@ assert chars(buffer, expected_size, append(cont_cs, hmac_cs));
    
    //Check the message tag hmac
    //@ chars_split(buffer, 1);
    if (buffer[0] != '0') abort();
    //@ close chars(buffer, 1, cons('0', nil));
    
    //Retrieve the actual request
    //@ assert chars((void*) buffer + 1, PACKAGE_SIZE, ?req_cs);
    //@ chars_to_crypto_chars((void*) buffer + 1, PACKAGE_SIZE);
    crypto_memcpy(request, (void*) buffer + 1, PACKAGE_SIZE);
    //@ cs_to_ccs_crypto_chars(request, req_cs);
    
    /*@ switch (cont_cs)
        {
          case cons(c1, cs1):
            assert cont_cs == cons('0', req_cs);
            if (!col && c1 == '0' && !bad(client))
            {
              public_ccs_cg(hmac_cg);
              open [_]rpc_pub(hmac_cg);
              assert [_]exists(?cont_cs');
              cs_to_ccs_inj(cont_cs, cont_cs');
              assert (true == request(client, server, req_cs));
            }
          case nil:
            assert false;
        }
    @*/
    //@ chars_to_crypto_chars((void*) buffer + 1 + PACKAGE_SIZE, 64);
    //@ crypto_chars_join((void*) buffer + 1);
    //@ crypto_chars_to_chars((void*) buffer + 1, PACKAGE_SIZE + 64);
    //@ chars_join(buffer);
  }

  //@ assert chars(request, PACKAGE_SIZE, ?req_cs);
  //@ close principal(server, _);
  compute_response(request, response);
  //@ open principal(server, _);
  //@ assert chars(response, PACKAGE_SIZE, ?resp_cs);

  {
    char hmac[64];

    size_t message_len = 1U + 2U * PACKAGE_SIZE + 64;
    char* message = malloc(message_len);
    if (message == 0) abort();
    //@ chars__split(message, 1 + 2 * PACKAGE_SIZE);

    *message = '1';
    //@ chars_to_crypto_chars(message, 1);
    //@ chars__split(message + 1, PACKAGE_SIZE);
    //@ chars_to_crypto_chars(request, PACKAGE_SIZE);
    crypto_memcpy(message + 1, request, PACKAGE_SIZE);
    //@ cs_to_ccs_crypto_chars(request, req_cs);
    //@ chars_to_crypto_chars(response, PACKAGE_SIZE);
    crypto_memcpy(message + 1 + PACKAGE_SIZE, response, PACKAGE_SIZE);
    //@ cs_to_ccs_crypto_chars(response, resp_cs);
    //@ crypto_chars_join(message + 1);
    //@ crypto_chars_join(message);
    //@ cs_to_ccs_append(req_cs, resp_cs);
    //@ list<char> pay_cs = cons('1', append(req_cs, resp_cs));
    //@ cs_to_ccs_crypto_chars(message, pay_cs);
    
    //@ chars_to_crypto_chars(message, 1 + 2 * PACKAGE_SIZE);
    //@ assert crypto_chars(normal, message, 1 + 2 * PACKAGE_SIZE, ?pay_ccs);
    //@ MEMCMP_PUB(message)
    sha512_hmac(key, (unsigned int) key_len, message,
                (unsigned int) 2 * PACKAGE_SIZE + 1, hmac, 0);
    //@ open cryptogram(hmac, 64, ?hmac_ccs, ?hmac_cg);
    //@ assert hmac_cg == cg_sha512_hmac(client, id, pay_ccs);
    crypto_memcpy(message + 1 + 2 * PACKAGE_SIZE, hmac, 64);
    //@ close cryptogram(message + 1 + 2 * PACKAGE_SIZE, 64, hmac_ccs, hmac_cg);
    //@ drop_append(PACKAGE_SIZE, req_cs, resp_cs);
    //@ take_append(PACKAGE_SIZE, req_cs, resp_cs);
    //@ close exists(pay_cs);
    //@ close rpc_pub(hmac_cg);
    //@ leak rpc_pub(hmac_cg);
    //@ public_cryptogram(message + 1 + 2 * PACKAGE_SIZE, hmac_cg);
    //@ crypto_chars_to_chars(message, 1 + 2 * PACKAGE_SIZE);
    //@ assert chars(message, message_len, _);

    net_send(&socket2, message, (unsigned int) message_len);
    free((void*) message);
    //@ close cryptogram(hmac, 64, hmac_ccs, hmac_cg);
    //@ public_cryptogram(hmac, hmac_cg);
  }

  net_close(socket2);
  net_close(socket1);
  //@ close principal(server, _);
}
