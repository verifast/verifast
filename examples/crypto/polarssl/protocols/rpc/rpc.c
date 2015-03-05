#include "rpc.h"

#include <stdlib.h>
#include <string.h>

//@ #include "quantifiers.gh"

#define SERVER_PORT 121212

void client(char *key, int key_len, char *request, char *response)
  /*@ requires [?f0]polarssl_world(rpc_polarssl_pub) &*&
               [?f1]polarssl_cryptogram(key, key_len, ?key_cs, ?key_cg) &*&
                 key_cg == polarssl_symmetric_key(?creator, ?id) &*&
               [?f2]polarssl_public_message(rpc_polarssl_pub)
                                           (request, PACKAGE_BYTE_SIZE, ?req_cs) &*&
               request(creator, shared_with(creator, id), req_cs) == true &*&
               chars(response, PACKAGE_BYTE_SIZE, _);
  @*/
  /*@ ensures  [f0]polarssl_world(rpc_polarssl_pub) &*&
               [f1]polarssl_cryptogram(key, key_len, key_cs, key_cg) &*&
               [f2]polarssl_public_message(rpc_polarssl_pub)
                                          (request, PACKAGE_BYTE_SIZE, req_cs) &*&
               polarssl_public_message(rpc_polarssl_pub)
                                      (response, PACKAGE_BYTE_SIZE, ?resp_cs) &*&
               bad(creator) || bad(shared_with(creator, id)) ?
                 true
               :
                 response(creator, shared_with(creator, id), req_cs, resp_cs) == true;
  @*/
{
  int socket;
  
  net_usleep(20000);
  if(net_connect(&socket, NULL, SERVER_PORT) != 0)
    abort();
  if(net_set_block(socket) != 0)
    abort();
  
  /*@ open [f2]polarssl_public_message(rpc_polarssl_pub)
                                      (request, PACKAGE_BYTE_SIZE, req_cs); @*/
  {
    char hmac[64];
    int message_len = 1 + PACKAGE_BYTE_SIZE + 64;
    char* message = malloc(message_len);
    if (message == 0) abort();
    
    *message = '0';
    memcpy(message + 1, request, PACKAGE_BYTE_SIZE);
    /*@ polarssl_generated_public_cryptograms_assume(rpc_polarssl_pub, 
                                                     cons('0', nil)); @*/
    /*@ polarssl_cryptograms_in_chars_public_upper_bound_join(
                                  rpc_polarssl_pub, cons('0', nil), req_cs); @*/
    //@ assert chars(message, PACKAGE_BYTE_SIZE + 1, cons('0', req_cs));
    //@ open [f1]polarssl_cryptogram(key, key_len, key_cs, key_cg);
    //@ close exists<polarssl_cryptogram>(key_cg);
    sha512_hmac(key, (unsigned int) key_len, message, 
                (unsigned int) PACKAGE_BYTE_SIZE + 1, hmac, 0);
    //@ close [f1]polarssl_cryptogram(key, key_len, key_cs, key_cg);
    //@ open polarssl_cryptogram(hmac, 64, ?hmac_cs, ?hmac_cg);
    memcpy(message + PACKAGE_BYTE_SIZE + 1, hmac, 64);

    //@ close rpc_polarssl_pub(hmac_cg);
    //@ leak rpc_polarssl_pub(hmac_cg);
    //@ polarssl_generated_public_cryptograms_upper_bound(rpc_polarssl_pub, hmac_cg);
    /*@ polarssl_cryptograms_in_chars_public_upper_bound_join(
                 rpc_polarssl_pub, append(cons('0', nil), req_cs), hmac_cs); @*/
    //@ chars_join(message);
    /*@ close polarssl_public_message(rpc_polarssl_pub)
                                     (message, message_len, 
                                      append(cons('0', req_cs), hmac_cs)); @*/
    net_send(&socket, message, (unsigned int) message_len);
    //@ open polarssl_public_message(rpc_polarssl_pub)(message, _, _);
    free(message);
  }
  
  {
    int size;
    char request2[PACKAGE_BYTE_SIZE];
    char hmac[64];
    char buffer[POLARSSL_MAX_MESSAGE_BYTE_SIZE];
    size = net_recv(&socket, buffer, POLARSSL_MAX_MESSAGE_BYTE_SIZE);
    if (size != 1 + 2 * PACKAGE_BYTE_SIZE + 64) abort();
    //@ open polarssl_public_message(rpc_polarssl_pub)(buffer, size, ?cs);

    //Verify the hmac
    /*@ polarssl_cryptograms_in_chars_public_upper_bound_split(
                           rpc_polarssl_pub, cs, 1 + 2 * PACKAGE_BYTE_SIZE); @*/
    /*@ assert chars(buffer, (1 + 2 * PACKAGE_BYTE_SIZE), 
                     take((1 + 2 * PACKAGE_BYTE_SIZE), cs)); @*/
    //@ open [f1]polarssl_cryptogram(key, key_len, key_cs, key_cg);
    //@ close exists<polarssl_cryptogram>(key_cg);
    sha512_hmac(key, (unsigned int) key_len, buffer, 
                (unsigned int) (1 + 2 * PACKAGE_BYTE_SIZE), hmac, 0);
    //@ close [f1]polarssl_cryptogram(key, key_len, key_cs, key_cg);
    //@ open polarssl_cryptogram(hmac, 64, ?hmac_cs, ?hmac_cg);
    if (memcmp(hmac, (void*) buffer + 1 + 2 * PACKAGE_BYTE_SIZE, 64) != 0) abort();

    //@ assert chars(buffer, 1 + 2 * PACKAGE_BYTE_SIZE, ?cont_cs);
    //@ assert chars(buffer, size, ?msg_cs);
    //@ assert msg_cs == append(cont_cs, hmac_cs);
    //@ assert hmac_cg == polarssl_hmac(creator, id, cont_cs);
    
    //Check the message tag hmac
    if (buffer[0] != '1') abort();
    //@ assert chars(buffer, 1, cons('1', nil));
    
    //Check if response is for the correct request
    //@ chars_split(buffer, 1);
    if (memcmp(request, (void*) buffer + 1, PACKAGE_BYTE_SIZE) != 0) abort();
    
    //Retrieve the actual response
    //@ chars_split((void*) buffer + 1, PACKAGE_BYTE_SIZE);
    memcpy(response, (void*) buffer + 1 + PACKAGE_BYTE_SIZE, PACKAGE_BYTE_SIZE);
    //@ assert chars(response, PACKAGE_BYTE_SIZE, ?resp_cs);
    //@ assert cont_cs == cons('1', append(req_cs, resp_cs));
    
    //@ chars_join((void*) buffer + 1 + PACKAGE_BYTE_SIZE);
    //@ chars_join((void*) buffer + 1);
    //@ chars_join((void*) buffer);
    //@ chars_join((void*) buffer);
    
    /*@ if (!bad(creator) && 
            !bad(shared_with(creator, id)))
        {
          switch (cont_cs) 
          {
            case cons(c1, cs1):
              if (c1 == '1')
              {
                polarssl_cryptograms_in_chars_public_upper_bound_split(
                           rpc_polarssl_pub, msg_cs, 1 + 2 * PACKAGE_BYTE_SIZE);
                polarssl_cryptogram_constraints(hmac_cs, hmac_cg);
                polarssl_cryptogram_in_upper_bound(hmac_cs, hmac_cg,
                       polarssl_generated_public_cryptograms(rpc_polarssl_pub));
                polarssl_generated_public_cryptograms_from(rpc_polarssl_pub, 
                                                           hmac_cg);
                open [_]rpc_polarssl_pub(hmac_cg);
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
    /*@ polarssl_cryptograms_in_chars_public_upper_bound_split(
                           rpc_polarssl_pub, cs, 1 + 2 * PACKAGE_BYTE_SIZE); @*/
    /*@ polarssl_cryptograms_in_chars_public_upper_bound_split(
                           rpc_polarssl_pub, cont_cs,1 + PACKAGE_BYTE_SIZE); @*/
    /*@ close polarssl_public_message(rpc_polarssl_pub)
                                     (response, PACKAGE_BYTE_SIZE, resp_cs); @*/
  }
  
  /*@ close [f2]polarssl_public_message(rpc_polarssl_pub)
                                       (request, PACKAGE_BYTE_SIZE, req_cs); @*/
  net_close(socket);
}

// This function represents the server application.
// We pass the key predicate just to get hold of the creator principal id.
void compute_response(char* request, char* response)
  /*@ requires [?f0]polarssl_world(rpc_polarssl_pub) &*&
               [?f1]polarssl_cryptogram(?key, ?key_len, ?key_cs, ?key_cg) &*&
                 key_cg == polarssl_symmetric_key(?creator, ?id) &*&
               polarssl_generated_values(shared_with(creator, id), ?count) &*&
               [?f2]chars(request, PACKAGE_BYTE_SIZE, ?req_cs) &*&
               chars(response, PACKAGE_BYTE_SIZE, _) &*&
               (
                 bad(creator) || 
                 bad(shared_with(creator, id)) ||
                 request(creator, shared_with(creator, id), req_cs)
               );
  @*/
  /*@ ensures  [f0]polarssl_world(rpc_polarssl_pub) &*&
               [f1]polarssl_cryptogram(key, key_len, key_cs, key_cg) &*&
                 polarssl_generated_values(shared_with(creator, id), count + 1) &*&
               [f2]chars(request, PACKAGE_BYTE_SIZE, req_cs) &*&
               polarssl_public_message(rpc_polarssl_pub)
                                      (response, PACKAGE_BYTE_SIZE, ?resp_cs) &*&
               response(creator, shared_with(creator, id), req_cs, resp_cs) == true;
  @*/
{
  havege_state havege_state;
  //@ close havege_state(&havege_state);
  havege_init(&havege_state);
  
  //@ close random_request(shared_with(creator, id), 0, false);
  if (havege_random(&havege_state, response, PACKAGE_BYTE_SIZE) != 0) abort();
  //@ open polarssl_cryptogram(response, PACKAGE_BYTE_SIZE, ?resp_cs, ?resp_cg);
  
  //@ polarssl_generated_public_cryptograms_assume(rpc_polarssl_pub, resp_cs);
  /*@ close polarssl_public_message(rpc_polarssl_pub)
                                   (response, PACKAGE_BYTE_SIZE, resp_cs); @*/
  //@ assume (response(creator, shared_with(creator, id), req_cs, resp_cs) == true);
  
  havege_free(&havege_state);
  //@ open havege_state(&havege_state);
}

void server(char *key, int key_len)
  /*@ requires [?f0]polarssl_world(rpc_polarssl_pub) &*&
               [?f1]polarssl_cryptogram(key, key_len, ?key_cs, ?key_cg) &*&
                 key_cg == polarssl_symmetric_key(?creator, ?id) &*&
               polarssl_generated_values(shared_with(creator, id), ?count);
  @*/
  /*@ ensures  [f0]polarssl_world(rpc_polarssl_pub) &*&
               [f1]polarssl_cryptogram(key, key_len, key_cs, key_cg) &*&
               polarssl_generated_values(shared_with(creator, id), count + 1);
  @*/
{
  int socket1;
  int socket2;
   
  if(net_bind(&socket1, NULL, SERVER_PORT) != 0)
    abort();
  if(net_accept(socket1, &socket2, NULL) != 0)
    abort();
  if(net_set_block(socket2) != 0)
    abort();
  
  char request[PACKAGE_BYTE_SIZE];
  char response[PACKAGE_BYTE_SIZE];
  
  //@ predicate(polarssl_cryptogram) req_cgs;
  {
    int size;
    char buffer[POLARSSL_MAX_MESSAGE_BYTE_SIZE];
    char hmac[64];
    size = net_recv(&socket2, buffer, POLARSSL_MAX_MESSAGE_BYTE_SIZE);
    if (size != 1 + PACKAGE_BYTE_SIZE + 64) abort();
    /*@ open polarssl_public_message(rpc_polarssl_pub)
                                    (buffer, size, ?cs); @*/

    //Verify the hmac
    /*@ polarssl_cryptograms_in_chars_public_upper_bound_split(
                               rpc_polarssl_pub, cs, 1 + PACKAGE_BYTE_SIZE); @*/
    /*@ assert chars(buffer, (1 + PACKAGE_BYTE_SIZE),
                     take((1 + PACKAGE_BYTE_SIZE), cs)); @*/
    //@ open [f1]polarssl_cryptogram(key, key_len, key_cs, key_cg);
    //@ close exists<polarssl_cryptogram>(key_cg);
    sha512_hmac(key, (unsigned int) key_len, buffer, 
                (unsigned int) (1 + PACKAGE_BYTE_SIZE), hmac, 0);
    //@ close [f1]polarssl_cryptogram(key, key_len, key_cs, key_cg);
    //@ open polarssl_cryptogram(hmac, 64, ?hmac_cs, ?hmac_cg);
    if (memcmp(hmac, (void*) buffer + 1 + PACKAGE_BYTE_SIZE, 64) != 0) abort();

    //@ assert chars(buffer, size, ?msg_cs);
    //@ assert chars(buffer, 1 + PACKAGE_BYTE_SIZE, ?cont_cs);
    //@ assert msg_cs == append(cont_cs, hmac_cs);
    //@ assert hmac_cg == polarssl_hmac(creator, id, cont_cs);
    
    //Check the message tag hmac
    if (buffer[0] != '0') abort();  
    
    //@ chars_split(buffer, 1);
    memcpy(request, (void*) buffer + 1, PACKAGE_BYTE_SIZE);
    //@ chars_join((void*) buffer + 1);
    //@ chars_join(buffer);
    
    /*@ switch (cont_cs) 
        {
          case cons(c1, cs1):
            assert chars(request, PACKAGE_BYTE_SIZE, ?req_cs);
            assert cont_cs == cons('0', req_cs);
            polarssl_cryptograms_in_chars_public_upper_bound_split(
                                                  rpc_polarssl_pub, cont_cs, 1);
            if (c1 == '0' && !bad(creator) && !bad(shared_with(creator, id)))
            {
              polarssl_cryptograms_in_chars_public_upper_bound_split(
                               rpc_polarssl_pub, msg_cs, 1 + PACKAGE_BYTE_SIZE);
              polarssl_cryptogram_in_upper_bound(hmac_cs, hmac_cg,
                       polarssl_generated_public_cryptograms(rpc_polarssl_pub));
              polarssl_generated_public_cryptograms_from(rpc_polarssl_pub, 
                                                         hmac_cg);
              open [_]rpc_polarssl_pub(hmac_cg);
              assert (request(creator, shared_with(creator, id), req_cs) == true);
           }
          case nil:
            assert false;
        }
    @*/
  }

  compute_response(request, response);
  //@ assert chars(request, PACKAGE_BYTE_SIZE, ?req_cs);
  /*@ open polarssl_public_message(rpc_polarssl_pub)
                                  (response, PACKAGE_BYTE_SIZE, ?resp_cs); @*/
  {
    char hmac[64];
    int message_len = 1 + 2 * PACKAGE_BYTE_SIZE + 64;
    char* message = malloc(message_len);
    if (message == 0) abort();
    
    *message = '1';
    memcpy(message + 1, request, PACKAGE_BYTE_SIZE);
    memcpy(message + 1 + PACKAGE_BYTE_SIZE, response, PACKAGE_BYTE_SIZE);
    /*@ polarssl_generated_public_cryptograms_assume(rpc_polarssl_pub,
                                                     cons('1', nil)); @*/
    /*@ polarssl_cryptograms_in_chars_public_upper_bound_join(
                                  rpc_polarssl_pub, cons('1', nil), req_cs); @*/
    /*@ polarssl_cryptograms_in_chars_public_upper_bound_join(
                 rpc_polarssl_pub, append(cons('1', nil), req_cs), resp_cs); @*/
    /*@ assert true == polarssl_cryptograms_in_chars_upper_bound(
                   cons('1', append(req_cs, resp_cs)), 
                   polarssl_generated_public_cryptograms(rpc_polarssl_pub)); @*/
    /*@ assert chars(message, 1 + 2 * PACKAGE_BYTE_SIZE, 
                               cons('1', append(req_cs, resp_cs))); @*/
    //@ open [f1]polarssl_cryptogram(key, key_len, key_cs, key_cg);
    //@ close exists<polarssl_cryptogram>(key_cg);
    sha512_hmac(key, (unsigned int) key_len, message, 
                (unsigned int) 2 * PACKAGE_BYTE_SIZE + 1, hmac, 0);
    //@ close [f1]polarssl_cryptogram(key, key_len, key_cs, key_cg);
    //@ assert chars(message, 1 + 2 * PACKAGE_BYTE_SIZE, ?cont_cs);
    //@ open polarssl_cryptogram(hmac, 64, ?hmac_cs, ?hmac_cg);
    memcpy(message + 2 * PACKAGE_BYTE_SIZE + 1, hmac, 64);
    //@ assert chars(message, message_len, ?msg_cs);
    //@ assert hmac_cg == polarssl_hmac(creator, id, cont_cs);

    //@ assert cont_cs == cons('1', append(req_cs, resp_cs));
    //@ drop_append(PACKAGE_BYTE_SIZE, req_cs, resp_cs);
    //@ take_append(PACKAGE_BYTE_SIZE, req_cs, resp_cs);

    //@ close rpc_polarssl_pub(hmac_cg);    
    //@ leak rpc_polarssl_pub(hmac_cg);
    //@ polarssl_generated_public_cryptograms_to(rpc_polarssl_pub, hmac_cg);
    /*@ polarssl_generated_public_cryptograms_upper_bound(rpc_polarssl_pub, 
                                                          hmac_cg); @*/
    /*@ polarssl_cryptograms_in_chars_public_upper_bound_join(rpc_polarssl_pub,
                  append(append(cons('1', nil), req_cs), resp_cs), hmac_cs); @*/
    /*@ close polarssl_public_message(rpc_polarssl_pub)(message, message_len,
                       append(append(cons('1', req_cs), resp_cs), hmac_cs)); @*/
    net_send(&socket2, message, (unsigned int) message_len);
    //@ open polarssl_public_message(rpc_polarssl_pub)(message, _, _);
    free(message);
  }
  
  net_close(socket2);
  net_close(socket1);
}
