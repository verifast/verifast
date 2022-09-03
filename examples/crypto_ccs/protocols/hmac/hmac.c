#include "hmac.h"

#include <stdlib.h>
#include <string.h>

//@ #include "quantifiers.gh"

#define SERVER_PORT 121212

void sender(char *key, int key_len, char *message)
  /*@ requires [_]public_invar(hmac_pub) &*&
               principal(?sender, _) &*&
               [?f1]cryptogram(key, key_len, ?key_ccs, ?key_cg) &*&
                 key_cg == cg_symmetric_key(sender, ?id) &*&
               [?f2]chars(message, MESSAGE_SIZE, ?msg_cs) &*&
               true == send(sender, shared_with(sender, id), msg_cs); @*/
  /*@ ensures  principal(sender, _) &*&
               [f1]cryptogram(key, key_len, key_ccs, key_cg) &*&
               [f2]chars(message, MESSAGE_SIZE, msg_cs); @*/
{
  //@ open principal(sender, _);
  int socket;
  char hmac[64];
  
  net_usleep(20000);
  if(net_connect(&socket, NULL, SERVER_PORT) != 0)
    abort();
  if(net_set_block(socket) != 0)
    abort();
  
  {
    size_t message_len = MESSAGE_SIZE + 64U;
    char* M = malloc(message_len);
    if (M == 0) abort();
    
    //@ chars_to_crypto_chars(message, MESSAGE_SIZE);
    crypto_memcpy(M, message, MESSAGE_SIZE);
    //@ MEMCMP_PUB(M)
    sha512_hmac(key, (unsigned int) key_len, M, 
                (unsigned int) MESSAGE_SIZE, hmac, 0);
    //@ assert cryptogram(hmac, 64, ?hmac_ccs, ?hmac_cg);
    //@ close exists(msg_cs);
    //@ close hmac_pub(hmac_cg);
    //@ leak hmac_pub(hmac_cg);
    //@ public_cryptogram(hmac, hmac_cg);
    //@ chars_to_crypto_chars(hmac, 64);
    crypto_memcpy(M + MESSAGE_SIZE, hmac, 64);
    //@ crypto_chars_to_chars(hmac, 64);
    
    //@ crypto_chars_to_chars(M, MESSAGE_SIZE);
    //@ crypto_chars_to_chars(M + MESSAGE_SIZE, 64);
    //@ chars_join(M);
    net_send(&socket, M, (unsigned int) message_len);
    free(M);
  }
  net_close(socket);
  //@ cs_to_ccs_crypto_chars(message, msg_cs);
  //@ close principal(sender, _);
}

void receiver(char *key, int key_len, char *message)
  /*@ requires [_]public_invar(hmac_pub) &*&
               principal(?receiver, _) &*&
               [?f1]cryptogram(key, key_len, ?key_ccs, ?key_cg) &*&
                 key_cg == cg_symmetric_key(?sender, ?id) &*&
                 receiver == shared_with(sender, id) &*&
               chars_(message, MESSAGE_SIZE, _); @*/
  /*@ ensures  principal(receiver, _) &*&
               [f1]cryptogram(key, key_len, key_ccs, key_cg) &*&
               chars(message, MESSAGE_SIZE, ?msg_cs) &*&
               col || bad(sender) || bad(receiver) ||
               send(sender, receiver, msg_cs); @*/
{
  //@ open principal(receiver, _);
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
    int expected_size = MESSAGE_SIZE + 64;
    if (size != expected_size) abort();
    //@ assert chars(buffer, MESSAGE_SIZE, ?msg_cs);
    
    //Verify the hmac
    //@ chars_to_crypto_chars(buffer, MESSAGE_SIZE);
    //@ MEMCMP_PUB(buffer)
    sha512_hmac(key, (unsigned int) key_len, buffer, 
                (unsigned int) MESSAGE_SIZE, hmac, 0);
    crypto_memcpy(message, (void*) buffer , MESSAGE_SIZE);
    //@ open cryptogram(hmac, 64, ?hmac_ccs, ?hmac_cg);
    //@ assert hmac_cg == cg_sha512_hmac(sender, id, _);
    //@ assert chars((void*) buffer + MESSAGE_SIZE, 64, _);
    //@ public_chars((void*) buffer + MESSAGE_SIZE, 64);
    //@ chars_to_crypto_chars((void*) buffer + MESSAGE_SIZE, 64);
    //@ MEMCMP_SEC(hmac, hmac_cg)
    //@ MEMCMP_PUB((void*) buffer + MESSAGE_SIZE)
    if (crypto_memcmp((void*) buffer + MESSAGE_SIZE, hmac, 64) != 0) abort();
    //@ crypto_chars_join(buffer);
    //@ crypto_chars_to_chars(buffer, expected_size);
    //@ public_crypto_chars(hmac, 64);
    
    /*@ if (!col && !bad(sender) && !bad(receiver))
        {  
          public_ccs_cg(hmac_cg);
          open [_]hmac_pub(hmac_cg);
          assert [_]exists(?msg_cs');
          cs_to_ccs_inj(msg_cs, msg_cs');
          assert (send(sender, receiver, msg_cs) == true); 
        }
    @*/
    //@ cs_to_ccs_crypto_chars(message, msg_cs);
  }
  net_close(socket2);
  net_close(socket1);
  //@ close principal(receiver, _);
}