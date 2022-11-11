#include "sign.h"

#include <stdlib.h>
#include <string.h>

//@ #include "quantifiers.gh"

#define SERVER_PORT 121212

int random_stub_sign(void *havege_state, char *output, size_t len)
  //@ requires PRG_PRECONDITION(havege_state_initialized, havege_state);
  //@ ensures PRG_POSTCONDITION(havege_state_initialized, havege_state);
{
  return havege_random(havege_state, output, len);
}

void sender(int recvr, char *key, int key_len, char *msg)
  /*@ requires [_]public_invar(sign_pub) &*&
               principal(?sender, _) &*&
               [?f1]cryptogram(key, key_len, ?key_ccs, ?key_cg) &*&
                 key_cg == cg_rsa_private_key(sender, ?id) &*&
                 key_len >= 512 &*& key_len < MAX_KEY_SIZE &*&
               [?f2]chars(msg, MSG_SIZE, ?msg_cs) &*&
               true == send(sender, recvr, msg_cs); @*/
  /*@ ensures  principal(sender, _) &*&
               [f1]cryptogram(key, key_len, key_ccs, key_cg) &*&
               [f2]chars(msg, MSG_SIZE, msg_cs); @*/
{
  //@ open principal(sender, _);
  int socket;
  char hash[64];
  pk_context context;
  havege_state havege_state;

  net_usleep(20000);
  if(net_connect(&socket, NULL, SERVER_PORT) != 0)
    abort();
  if(net_set_block(socket) != 0)
    abort();

  {
    size_t sign_len;
    int max_message_len = 4 + MSG_SIZE + key_len;
    char* M = malloc((size_t)max_message_len);
    if (M == 0) abort();

    // fill in plain text
    //@ assert integer(&recvr, ?receiver);
    //@ integer_to_chars(&recvr);
    //@ chars_to_crypto_chars((void*) &recvr, 4);
    crypto_memcpy(M, &recvr, 4);
    //@ cs_to_ccs_crypto_chars((void*) &recvr, chars_of_int(receiver));
    //@ chars_to_integer(&recvr);
    
    //@ chars_to_crypto_chars(msg, MSG_SIZE);
    crypto_memcpy(M + 4, msg, (unsigned int) MSG_SIZE);
    //@ crypto_chars_join(M);
    //@ list<char> pay = append(chars_of_int(receiver), msg_cs);
    //@ cs_to_ccs_crypto_chars(msg, msg_cs);
    //@ cs_to_ccs_append(chars_of_int(receiver), msg_cs);
    //@ cs_to_ccs_crypto_chars(M, pay);

    // create hash of plain text
    //@ assert chars(M, 4 + MSG_SIZE, pay);
    //@ chars_to_crypto_chars(M, 4 + MSG_SIZE);
    //@ MEMCMP_PUB(M)
    sha512(M, (unsigned int) (4 + MSG_SIZE), hash, 0);
    //@ open cryptogram(hash, 64, ?hash_cs, ?hash_cg);
    //@ close cryptogram(hash, 64, hash_cs, hash_cg);
    //@ close sign_pub(hash_cg);
    //@ leak sign_pub(hash_cg);
    //@ public_cryptogram(hash, hash_cg);
    //@ chars_to_crypto_chars(hash, 64);

    // create signature
    //@ close pk_context(&context);
    pk_init(&context);
    if (pk_parse_key(&context, key, (unsigned int) key_len, NULL, 0) != 0)
      abort();
    //@ close havege_state(&havege_state);
    havege_init(&havege_state);
    //@ close random_state_predicate(havege_state_initialized);
    /*@ produce_function_pointer_chunk random_function(random_stub_sign)
                     (havege_state_initialized)(state, out, len) { call(); } @*/
    if (pk_sign(&context, MBEDTLS_MD_NONE, hash, 64, M + 4 + MSG_SIZE,
                &sign_len, random_stub_sign, &havege_state) != 0)
      abort();
    //@ pk_release_context_with_key(&context);
    pk_free(&context);
    //@ open pk_context(&context);
    havege_free(&havege_state);
    //@ open havege_state(&havege_state);
    //@ assert sign_len |-> ?sign_len_val;
    //@ crypto_chars_to_chars(hash, 64);
    //@ open cryptogram(M + 4 + MSG_SIZE, sign_len_val, ?cs_sign, ?cg_sign);
    //@ close cryptogram(M + 4 + MSG_SIZE, sign_len_val, cs_sign, cg_sign);
    //@ assert cg_sign == cg_rsa_signature(sender, id, hash_cs, _);
    //@ if (!col && !bad(sender)) close sign_pub_1(msg_cs, recvr);
    
    //@ close sign_pub(cg_sign);
    //@ leak sign_pub(cg_sign);
    //@ public_cryptogram(M + 4 + MSG_SIZE, cg_sign);
    int message_len = 4 + MSG_SIZE + (int) sign_len;
    //@ crypto_chars_to_chars(M, 4 + MSG_SIZE);
    //@ chars_join(M);
    net_send(&socket, M, (unsigned int) message_len);
    free(M);
  }
  net_close(socket);
  //@ close principal(sender, _);
}

void receiver(int recvr, char *key, int key_len, char *msg)
  /*@ requires [_]public_invar(sign_pub) &*&
               principal(recvr, _) &*&
               [?f1]cryptogram(key, key_len, ?key_ccs, ?key_cg) &*&
                 key_cg == cg_rsa_public_key(?sender, ?id) &*&
                 key_len <= MAX_KEY_SIZE &*&
               chars_(msg, MSG_SIZE, _); @*/
  /*@ ensures  principal(recvr, _) &*&
               [f1]cryptogram(key, key_len, key_ccs, key_cg) &*&
               chars(msg, MSG_SIZE, ?msg_cs) &*&
               col || bad(sender) ||
                 send(sender, recvr, msg_cs); @*/
{
  //@ open principal(recvr, _);
  int socket1;
  int socket2;

  if(net_bind(&socket1, NULL, SERVER_PORT) != 0)
    abort();
  if(net_accept(socket1, &socket2, NULL) != 0)
    abort();
  if(net_set_block(socket2) != 0)
    abort();

  {
    pk_context context;
    int max_size = 4 + MSG_SIZE + MAX_KEY_SIZE;
    char hash[64];
    int* temp;
    char *buffer = malloc ((size_t)max_size); if (buffer == 0) abort();
    int size = net_recv(&socket2, buffer, (unsigned int) max_size);
    if (size <= 4 + MSG_SIZE) abort();
    if (64 * 8 > key_len) abort();

    // Parse plain text
    //@ chars_split(buffer, 4);
    //@ chars_to_integer(buffer);
    temp = (void*) buffer;
    int receiver = *temp;
    if (recvr != receiver) abort();
    //@ integer_to_chars(buffer);
    //@ assert chars(buffer, 4, chars_of_int(receiver));
    //@ chars_split(buffer + 4, MSG_SIZE);
    //@ assert chars(buffer + 4, MSG_SIZE, ?msg_cs);
    //@ chars_to_crypto_chars(buffer + 4, MSG_SIZE);
    crypto_memcpy(msg, buffer + 4, MSG_SIZE);
    //@ cs_to_ccs_crypto_chars(msg, msg_cs);
    //@ cs_to_ccs_crypto_chars(buffer + 4, msg_cs);
    int sign_size = size - 4 - MSG_SIZE;
    //@ assert chars(buffer + 4 + MSG_SIZE, sign_size, ?sign_cs);

    // Calculate hash
    //@ chars_join(buffer);
    //@ assert chars(buffer, 4 + MSG_SIZE, ?pay);
    //@ chars_to_crypto_chars(buffer, 4 + MSG_SIZE);
    //@ assert pay == append(chars_of_int(receiver), msg_cs);
    //@ MEMCMP_PUB(buffer)
    sha512(buffer, (unsigned int) (4 + MSG_SIZE), hash, 0);
    //@ open cryptogram(hash, 64, ?hash_cs, ?hash_cg);
    //@ close sign_pub(hash_cg);
    //@ leak sign_pub(hash_cg);

    // Check signatrure
    //@ close pk_context(&context);
    pk_init(&context);
    if (pk_parse_public_key(&context, key, (unsigned int) key_len) != 0)
      abort();
    //@ assert chars(buffer + 4 + MSG_SIZE, sign_size, sign_cs);
    //@ interpret_asym_signature(buffer + 4 + MSG_SIZE, sign_size);
    if (pk_verify(&context, MBEDTLS_MD_NONE, hash, 64,
                  buffer + 4 + MSG_SIZE, (unsigned int) sign_size) != 0)
      abort();
    //@ open cryptogram(buffer + 4 + MSG_SIZE, sign_size, ?sign_ccs, ?sign_cg);
    //@ pk_release_context_with_key(&context);
    pk_free(&context);
    //@ open pk_context(&context);
    //@ close cryptogram(hash, 64, hash_cs, hash_cg);
    //@ public_cryptogram(hash, hash_cg);
    
    //@ public_crypto_chars(buffer + 4 + MSG_SIZE, sign_size);
    //@ assert chars(buffer + 4 + MSG_SIZE, sign_size, ?sign_cs');
    //@ cs_to_ccs_inj(sign_cs, sign_cs');
    
    /*@ if (!col && !bad(sender))
        {
          open [_]sign_pub(sign_cg);
          assert [_]sign_pub_1(?msg_cs2, ?receiver2);
          cryptogram hash_cg2 = 
            cg_sha512_hash(cs_to_ccs(append(chars_of_int(receiver2), msg_cs2)));
          ccs_for_cg_inj(hash_cg, hash_cg2);
          cs_to_ccs_inj(append(chars_of_int(receiver), msg_cs),
                        append(chars_of_int(receiver2), msg_cs2));
          assert true == send(sender, receiver2, msg_cs2);
          drop_append(4, chars_of_int(receiver), msg_cs);
          drop_append(4, chars_of_int(receiver2), msg_cs2);
          take_append(4, chars_of_int(receiver), msg_cs);
          take_append(4, chars_of_int(receiver2), msg_cs2);
          chars_of_int_injective(receiver, receiver2);
          assert true == send(sender, receiver, msg_cs);
        }
    @*/
    //@ cs_to_ccs_crypto_chars(buffer, pay);
    //@ assert chars(buffer, 4 + MSG_SIZE, pay);
    //@ assert chars(buffer + 4 + MSG_SIZE, sign_size, sign_cs);
    //@ chars_join(buffer);
    //@ append_assoc(chars_of_int(receiver), msg_cs, sign_cs);
    
    //@ assert chars(buffer, size, append(pay, sign_cs));
    free(buffer);
  }
  net_close(socket2);
  net_close(socket1);
  //@ close principal(recvr, _);
}
