#include "attacker.h"

#include "mbedTLS_definitions.h"

#define ATTACKER_ITERATIONS 100

/*@

predicate_ctor attacker_nonce_pred(predicate(cryptogram) pub,
                                   predicate() proof_pred)() =
  is_bad_nonce_is_public(_, pub, proof_pred) &*&
  proof_pred()
;

lemma void close_havege_util(predicate(cryptogram) pub,
                             predicate() pred, int principal)
  requires is_principal_with_public_nonces(_, pub,
                                           attacker_nonce_pred(pub, pred),
                                           principal) &*&
           is_bad_nonce_is_public(_, pub, pred) &*& pred();
  ensures  havege_util(pub, attacker_nonce_pred(pub, pred), principal);
{
  close attacker_nonce_pred(pub, pred)();
  close havege_util(pub, attacker_nonce_pred(pub, pred), principal);
}

lemma void open_havege_util(predicate(cryptogram) pub,
                            predicate() pred, int principal)
  requires havege_util(pub, attacker_nonce_pred(pub, pred), principal);
  ensures  is_principal_with_public_nonces(_, pub,
                                           attacker_nonce_pred(pub, pred),
                                           principal) &*&
           is_bad_nonce_is_public(_, pub, pred) &*&
           pred();
{
  open havege_util(pub, attacker_nonce_pred(pub, pred), principal);
  open attacker_nonce_pred(pub, pred)();
}

predicate attacker_invariant(predicate(cryptogram) pub,
                             predicate() pred,
                             fixpoint(int, int, bool, bool) classifier,
                             struct havege_state* state,
                             void* socket, int attacker) =
  [_]public_invar(pub) &*& pred() &*&
  [_]decryption_key_classifier(classifier) &*&
  havege_state_initialized(state) &*&
  integer(socket, ?fd) &*& net_status(fd, ?ip, ?port, connected) &*&
  true == bad(attacker) &*&
  random_permission(attacker, _) &*&
  decryption_permission(attacker) &*&
  is_principal_with_public_nonces(_, pub,
                                  attacker_nonce_pred(pub, pred),
                                  attacker) &*&
    is_bad_nonce_is_public(_, pub, pred) &*&
    is_bad_key_is_public(_, pub, pred) &*&
    is_public_key_is_public(_, pub, pred) &*&
    is_bad_private_key_is_public(_, pub, pred) &*&
    is_hash_is_public(_, pub, pred) &*&
    is_public_hmac_is_public(_, pub, pred) &*&
    is_public_encryption_is_public(_, pub, pred) &*&
    is_public_decryption_is_public(_, pub, pred) &*&
    is_public_auth_encryption_is_public(_, pub, pred) &*&
    is_public_auth_decryption_is_public(_, pub, pred) &*&
    is_public_asym_encryption_is_public(_, pub, pred) &*&
    is_public_asym_decryption_is_public(_, pub, pred) &*&
    is_public_asym_signature_is_public(_, pub, pred) &*&
  is_public_key_classifier(_, pub, classifier, pred)
;

@*/

void get_random_bytes(char *buffer, size_t len)
//@ requires chars_(buffer, len, _);
//@ ensures chars(buffer, len, _);
{
  memset(buffer, 0, len);
}

void attacker_send_data(havege_state *havege_state, void* socket)
  //@ requires attacker_invariant(?pub, ?pred, ?kc, havege_state, socket, ?attacker);
  //@ ensures  attacker_invariant(pub, pred, kc, havege_state, socket, attacker);
{
  int temp;
  int size;
  char buffer[MAX_MESSAGE_SIZE];
  
  //@ open attacker_invariant(pub, pred, kc, havege_state, socket, attacker);
  //@ close_havege_util(pub, pred, attacker);
  r_int_with_bounds(havege_state, &temp, 1, MAX_MESSAGE_SIZE);
  //@ open_havege_util(pub, pred, attacker);
  size = temp;
  //@ chars__split(buffer, size);
  get_random_bytes(buffer, (unsigned int) size);
  net_send(socket, buffer, (unsigned int) size);
  //@ close attacker_invariant(pub, pred, kc, havege_state, socket, attacker);
  //@ chars_to_chars_(buffer);
}

void attacker_send_concatenation(havege_state *havege_state, void* socket)
  //@ requires attacker_invariant(?pub, ?pred, ?kc, havege_state, socket, ?attacker);
  //@ ensures  attacker_invariant(pub, pred, kc, havege_state, socket, attacker);
{
  int size1;
  int size2;
  char buffer1[MAX_MESSAGE_SIZE];
  char buffer2[MAX_MESSAGE_SIZE];
  char buffer3[MAX_MESSAGE_SIZE];

  //@ open attacker_invariant(pub, pred, kc, havege_state, socket, attacker);

  size1 = net_recv(socket, buffer1, MAX_MESSAGE_SIZE);
  size2 = net_recv(socket, buffer2, MAX_MESSAGE_SIZE);
  if (size1 <= 0 || size2 <= 0 || MAX_MESSAGE_SIZE - size1 <= size2)
  {
    //@ close attacker_invariant(pub, pred, kc, havege_state, socket, attacker);
    //@ chars_to_chars_(buffer1);
    //@ chars_to_chars_(buffer2);
    return;
  }

  //@ chars_to_crypto_chars(buffer1, size1);
  crypto_memcpy(buffer3, buffer1, (unsigned int) size1);
  //@ chars_to_crypto_chars(buffer2, size2);
  crypto_memcpy((char*) buffer3 + size1, buffer2, (unsigned int) size2);
  //@ crypto_chars_join(buffer3);
  //@ crypto_chars_to_chars(buffer3, size1 + size2);
  net_send(socket, buffer3, (unsigned int) (size1 + size2));
  //@ close attacker_invariant(pub, pred, kc, havege_state, socket, attacker);
  //@ crypto_chars_to_chars(buffer1, size1);
  //@ crypto_chars_to_chars(buffer2, size2);
}

void attacker_send_split(havege_state *havege_state, void* socket)
  //@ requires attacker_invariant(?pub, ?pred, ?kc, havege_state, socket, ?attacker);
  //@ ensures  attacker_invariant(pub, pred, kc, havege_state, socket, attacker);
{
  int temp;
  int size1;
  int size2;
  char buffer[MAX_MESSAGE_SIZE];

  //@ open attacker_invariant(pub, pred, kc, havege_state, socket, attacker);
  size1 = net_recv(socket, buffer, MAX_MESSAGE_SIZE);
  if (size1 <= 0)
  {
    //@ close attacker_invariant(pub, pred, kc, havege_state, socket, attacker);
    return;
  }
  //@ assert chars(buffer, size1, ?cs);

  //@ close_havege_util(pub, pred, attacker);
  r_int_with_bounds(havege_state, &temp, 0, size1);
  //@ open_havege_util(pub, pred, attacker);
  size2 = temp;
  net_send(socket, buffer, (unsigned int) (size2));
  net_send(socket, (void*) buffer + size2,
            (unsigned int) (size1 - size2));

  //@ chars_join(buffer);
  //@ close attacker_invariant(pub, pred, kc, havege_state, socket, attacker);
}

void attacker_send_random(havege_state *havege_state, void* socket)
  //@ requires attacker_invariant(?pub, ?pred, ?kc, havege_state, socket, ?attacker);
  //@ ensures  attacker_invariant(pub, pred, kc, havege_state, socket, attacker);
{
  int temp;
  int size;
  char buffer[MAX_MESSAGE_SIZE];

  //@ open attacker_invariant(pub, pred, kc, havege_state, socket, attacker);
  //@ close_havege_util(pub, pred, attacker);
  r_int_with_bounds(havege_state, &temp, MIN_RANDOM_SIZE, MAX_MESSAGE_SIZE);
  size = temp;
  r_int_with_bounds(havege_state, &temp, 0, INT_MAX);
  //@ open_havege_util(pub, pred, attacker);
  //@ close random_request(attacker, temp, false);
  if (havege_random(havege_state, buffer, (unsigned int) size) == 0)
  {
    //@ assert cryptogram(buffer, size, ?ccs, ?cg);
    //@ assert is_bad_nonce_is_public(?proof, pub, pred);
    //@ proof(cg);
    //@ public_cryptogram(buffer, cg);
    net_send(socket, buffer, (unsigned int) size);
  }
  //@ close attacker_invariant(pub, pred, kc, havege_state, socket, attacker);
}

int attacker_key_item_havege_random_stub(void *havege_state,
                                         char *output, size_t len)
  //@ requires PRG_PRECONDITION(havege_state_initialized, havege_state);
  //@ ensures PRG_POSTCONDITION(havege_state_initialized, havege_state);
{
  return havege_random(havege_state, output, len);
}

void attacker_send_keys(havege_state *havege_state, void* socket)
  //@ requires attacker_invariant(?pub, ?pred, ?kc, havege_state, socket, ?attacker);
  //@ ensures  attacker_invariant(pub, pred, kc, havege_state, socket, attacker);
{
  pk_context context;
  pk_context context_pub;
  pk_context context_priv;
  unsigned int key_size;

  //@ open attacker_invariant(pub, pred, kc, havege_state, socket, attacker);

  unsigned int temp;
  //@ close_havege_util(pub, pred, attacker);
  r_u_int_with_bounds(havege_state, &temp, 1024, 8192);
  //@ open_havege_util(pub, pred, attacker);
  key_size = temp;
  char* key = malloc(key_size);
  if ((key) == 0) abort();
  char* pub_key = malloc(key_size);
  if ((pub_key) == 0) abort();
  char* priv_key = malloc(key_size);
  if ((priv_key) == 0) abort();

  //@ close random_request(attacker, temp, true);
  if (havege_random(havege_state, key, key_size) != 0) abort();

  //@ close pk_context(&context);
  pk_init(&context);
  //@ close pk_context(&context_pub);
  pk_init(&context_pub);
  //@ close pk_context(&context_priv);
  pk_init(&context_priv);

  if (pk_init_ctx(&context, pk_info_from_type(MBEDTLS_PK_RSA)) != 0)
    abort();
  //@ close rsa_key_request(attacker, 0);
  //@ close random_state_predicate(havege_state_initialized);
  /*@ produce_function_pointer_chunk random_function(
                      attacker_key_item_havege_random_stub)
                     (havege_state_initialized)(state, out, len) { call(); } @*/
  if (rsa_gen_key(context.pk_ctx, attacker_key_item_havege_random_stub,
                  havege_state, key_size, 65537) != 0) abort();

  if (pk_write_pubkey_pem(&context, pub_key, key_size) != 0) abort();
  if (pk_write_key_pem(&context, priv_key, key_size) != 0) abort();
  if (pk_parse_public_key(&context_pub, pub_key, key_size) != 0) abort();
  if (pk_parse_key(&context_priv, priv_key, key_size, NULL, 0) != 0) abort();

  //@ assert is_bad_key_is_public(?proof1, pub, pred);
  //@ assert cryptogram(key, key_size, ?key_ccs, ?key_cg);
  //@ proof1(key_cg);
  //@ public_cryptogram(key, key_cg);
  net_send(socket, key, key_size);

  //@ assert is_public_key_is_public(?proof2, pub, pred);
  //@ assert cryptogram(pub_key, key_size, ?pub_key_ccs, ?pub_key_cg);
  //@ proof2(pub_key_cg);
  //@ public_cryptogram(pub_key, pub_key_cg);
  net_send(socket, pub_key, key_size);

  //@ assert is_bad_private_key_is_public(?proof3, pub, pred);
  //@ assert cryptogram(priv_key, key_size, ?priv_key_ccs, ?priv_key_cg);
  //@ proof3(priv_key_cg);
  //@ public_cryptogram(priv_key, priv_key_cg);
  net_send(socket, priv_key, key_size);

  //@ open random_state_predicate(havege_state_initialized);
  //@ pk_release_context_with_keys(&context);
  pk_free(&context);
  //@ open pk_context(&context);
  //@ pk_release_context_with_key(&context_pub);
  pk_free(&context_pub);
  //@ open pk_context(&context_pub);
  //@ pk_release_context_with_key(&context_priv);
  pk_free(&context_priv);
  //@ open pk_context(&context_priv);
  free(key);
  free(pub_key);
  free(priv_key);

  //@ close attacker_invariant(pub, pred, kc, havege_state, socket, attacker);
}

void attacker_send_hash(havege_state *havege_state, void* socket)
  //@ requires attacker_invariant(?pub, ?pred, ?kc, havege_state, socket, ?attacker);
  //@ ensures  attacker_invariant(pub, pred, kc, havege_state, socket, attacker);
{
  int temp;
  int size;
  char buffer[MAX_MESSAGE_SIZE];

  //@ open attacker_invariant(pub, pred, kc, havege_state, socket, attacker);

  size = net_recv(socket, buffer, MAX_MESSAGE_SIZE);
  if (size < MINIMAL_STRING_SIZE)
  {
    //@ close attacker_invariant(pub, pred, kc, havege_state, socket, attacker);
    return;
  }
  //@ assert chars(buffer, size, ?pay);

  char hash[64];
  //@ chars_to_crypto_chars(buffer, size);
  //@ MEMCMP_PUB(buffer)
  sha512(buffer, (unsigned int) size, hash, 0);
  //@ assert cryptogram(hash, 64, ?h_ccs, ?h_cg);
  //@ assert h_cg == cg_sha512_hash(cs_to_ccs(pay));
  //@ assert is_hash_is_public(?proof, pub, pred);
  //@ crypto_chars_to_chars(buffer, size);
  //@ public_chars(buffer, size);
  //@ proof(h_cg);
  //@ public_cryptogram(hash, h_cg);
  net_send(socket, hash, 64);

  //@ close attacker_invariant(pub, pred, kc, havege_state, socket, attacker);
}

void attacker_send_hmac(havege_state *havege_state, void* socket)
  //@ requires attacker_invariant(?pub, ?pred, ?kc, havege_state, socket, ?attacker);
  //@ ensures  attacker_invariant(pub, pred, kc, havege_state, socket, attacker);
{
  int temp;
  int size1;
  int size2;
  char buffer1[MAX_MESSAGE_SIZE];
  char buffer2[MAX_MESSAGE_SIZE];
  char buffer3[64];

  //@ open attacker_invariant(pub, pred, kc, havege_state, socket, attacker);

  size1 = net_recv(socket, buffer1, MAX_MESSAGE_SIZE);
  size2 = net_recv(socket, buffer2, MAX_MESSAGE_SIZE);
  if (size1 <= 0 || size2 < MINIMAL_STRING_SIZE)
  {
    //@ close attacker_invariant(pub, pred, kc, havege_state, socket, attacker);
    return;
  }

  //@ interpret_symmetric_key(buffer1, size1);
  //@ assert cryptogram(buffer1, size1, ?ccs1, cg_symmetric_key(?p, ?c));
  //@ assert chars(buffer2, size2, ?pay);
  //@ chars_to_crypto_chars(buffer2, size2);
  //@ public_cs(pay);
  //@ MEMCMP_PUB(buffer2)
  sha512_hmac(buffer1, (unsigned int) size1, buffer2,
              (unsigned int) size2, buffer3, 0);
  //@ assert cryptogram(buffer3, 64, ?ccs_hmac, ?hmac);
  //@ assert is_public_hmac_is_public(?proof2, pub, pred);
  //@ crypto_chars_to_chars(buffer2, size2);
  //@ public_chars(buffer2, size2);
  //@ proof2(hmac);
  //@ public_cryptogram(buffer3, hmac);
  net_send(socket, buffer3, 64);
  //@ public_cryptogram(buffer1, cg_symmetric_key(p, c));

  //@ close attacker_invariant(pub, pred, kc, havege_state, socket, attacker);
}

int get_iv(havege_state *state, char* iv)
  /*@ requires [_]public_invar(?pub) &*&
               havege_state_initialized(state) &*&
               random_permission(?p, ?c) &*& true == bad(p) &*&
               is_bad_nonce_is_public(?proof, pub, ?pred) &*&
               pred() &*& chars_(iv, 16, _);@*/
  /*@ ensures  havege_state_initialized(state) &*&
               random_permission(p, c + 1) &*&
               is_bad_nonce_is_public(proof, pub, pred) &*&
               pred() &*&
               result == 0 ?
                   crypto_chars(normal, iv, 16, ?ccs) &*& ccs == ccs_for_cg(cg_nonce(p, c + 1))
               :
                   chars_(iv, 16, _);@*/
{
  int result = -1;
  //@ close random_request(p, 0, false);
  if (havege_random(state, iv, 16) == 0)
  {
    //@ open cryptogram(iv, 16, ?ccs_iv, ?cg_iv);
    //@ close cryptogram(iv, 16, ccs_iv, cg_iv);
    //@ proof(cg_iv);
    //@ public_cryptogram(iv, cg_iv);
    //@ chars_to_crypto_chars(iv, 16);
    
    result = 0;
  }
  return result;
}

void attacker_send_encrypted(havege_state *havege_state, void* socket)
  //@ requires attacker_invariant(?pub, ?pred, ?kc, havege_state, socket, ?attacker);
  //@ ensures  attacker_invariant(pub, pred, kc, havege_state, socket, attacker);
{
  int temp;
  int size1;
  int size2;
  char buffer1[MAX_MESSAGE_SIZE];
  char buffer2[MAX_MESSAGE_SIZE];
  char buffer3[MAX_MESSAGE_SIZE];
  aes_context aes_context;
  size_t iv_off = 0;
  char iv[16];

  //@ open attacker_invariant(pub, pred, kc, havege_state, socket, attacker);

  size1 = net_recv(socket, buffer1, MAX_MESSAGE_SIZE);
  size2 = net_recv(socket, buffer2, MAX_MESSAGE_SIZE);
  if (size1 <= 0 || size2 < MINIMAL_STRING_SIZE ||
      (size1 != 16 && size1 != 24 && size1 != 32))
  {
    //@ close attacker_invariant(pub, pred, kc, havege_state, socket, attacker);
    return;
  }

  //@ close aes_context(&aes_context);
  //@ interpret_symmetric_key(buffer1, size1);
  //@ assert cryptogram(buffer1, size1, ?ccs1, ?cg_key);
  //@ assert cg_key == cg_symmetric_key(?p, ?c);
  if (aes_setkey_enc(&aes_context, buffer1, (unsigned int) size1 * 8) == 0)
  {
    if (get_iv(havege_state, iv) == 0)
    {
      //@ assert crypto_chars(normal, iv, 16, ?ccs_iv);
      //@ chars_to_crypto_chars(buffer2, size2);
      if (aes_crypt_cfb128(&aes_context, AES_ENCRYPT,
                            (unsigned int) size2, &iv_off, iv, buffer2,
                            buffer3) == 0)
      {
        /*@
          {
            assert cryptogram(buffer3, size2, ?ccs_enc, ?cg_enc);
            assert cg_enc == cg_aes_encrypted(p, c, ?cs2, ccs_iv);
            assert [_]pub(cg_key);
            assert is_public_encryption_is_public(?proof2, pub, pred);
            crypto_chars_to_chars(buffer2, size2);
            public_chars(buffer2, size2);
            proof2(cg_enc);
            public_cryptogram(buffer3, cg_enc);
            chars_to_crypto_chars(buffer2, size2);
          }
        @*/
        net_send(socket, buffer3, (unsigned int) size2);
      }
      //@ crypto_chars_to_chars(buffer2, size2);
      //@ crypto_chars_to_chars(iv, 16);
    }
    aes_free(&aes_context);
    //@ open aes_context(&aes_context);
    //@ close attacker_invariant(pub, pred, kc, havege_state, socket, attacker);
    //@ public_cryptogram(buffer1, cg_symmetric_key(p, c));
    return;
  }

  //@ open aes_context(&aes_context);
  //@ close attacker_invariant(pub, pred, kc, havege_state, socket, attacker);
  //@ public_cryptogram(buffer1, cg_symmetric_key(p, c));
  return;
}

void attacker_send_decrypted(havege_state *havege_state, void* socket)
  //@ requires attacker_invariant(?pub, ?pred, ?kc, havege_state, socket, ?attacker);
  //@ ensures  attacker_invariant(pub, pred, kc, havege_state, socket, attacker);
{
  int temp;
  int size1;
  int size2;
  char buffer1[MAX_MESSAGE_SIZE];
  char buffer2[MAX_MESSAGE_SIZE];
  char buffer3[MAX_MESSAGE_SIZE];
  aes_context aes_context;
  char iv[16];
  size_t iv_off = 0;

  //@ open attacker_invariant(pub, pred, kc, havege_state, socket, attacker);

  size1 = net_recv(socket, buffer1, MAX_MESSAGE_SIZE);
  size2 = net_recv(socket, buffer2, MAX_MESSAGE_SIZE);
  if (size1 <= 0 || size2 < MINIMAL_STRING_SIZE ||
       (size1 != 16 && size1 != 24 && size1 != 32))
  {
    //@ close attacker_invariant(pub, pred, kc, havege_state, socket, attacker);
    return;
  }

  //@ close aes_context(&aes_context);
  //@ interpret_symmetric_key(buffer1, size1);
  //@ assert cryptogram(buffer1, size1, ?ccs1, ?cg_key);
  //@ assert cg_key == cg_symmetric_key(?p, ?c);
  if (aes_setkey_enc(&aes_context, buffer1, (unsigned int) size1 * 8) == 0)
  {
    if (get_iv(havege_state, iv) == 0)
    {
      //@ assert crypto_chars(normal, iv, 16, ?ccs_iv);
      //@ interpret_encrypted(buffer2, size2);
      //@ open cryptogram(buffer2, size2, ?ccs2, ?cg_enc);
      //@ close cryptogram(buffer2, size2, ccs2, cg_enc);
      //@ assert cg_enc == cg_aes_encrypted(?p2, ?c2, ?ccs_output2, ?ccs_iv2);
      //@ structure s = known_value(0, nil);
      //@ close decryption_pre(true, false, attacker, s, ccs2);
      int success = aes_crypt_cfb128(&aes_context, AES_DECRYPT,
                                     (unsigned int) size2, &iv_off, iv,
                                     buffer2, buffer3);
      if (success == 0) zeroize(iv, 16); 
      //@ if (success == 0) chars_to_crypto_chars(iv, 16);
      //@ open decryption_post(true, ?garbage, attacker, s, p, c, ?ccs_output);
      /*@ if (garbage)
          {
            assert is_public_key_classifier(?proof, _, _, _);
            proof(cg_key, p, c, true);
            decryption_garbage(buffer3, size2, s);
          }
          else if (success == 0)
          {
            assert crypto_chars(secret, buffer3, size2, ccs_output);
            assert ccs_output == ccs_output2;
            assert ccs_iv == ccs_iv2;
            assert ccs2 == ccs_for_cg(cg_enc);
            public_ccs_cg(cg_enc);
            assert [_]pub(cg_enc);
            assert is_public_decryption_is_public(?proof2, pub, pred);
            proof2(cg_key, cg_enc);
            public_crypto_chars(buffer3, size2);
            chars_to_crypto_chars(buffer3, size2);
          }
      @*/
      //@ crypto_chars_to_chars(buffer3, size2);
      net_send(socket, buffer3, (unsigned int) size2);
      //@ public_cryptogram(buffer2, cg_enc);
      //@ crypto_chars_to_chars(iv, 16);
    }
    aes_free(&aes_context);
  }
  //@ open aes_context(&aes_context);
  //@ close attacker_invariant(pub, pred, kc, havege_state, socket, attacker);
  //@ public_cryptogram(buffer1, cg_key);
}

void attacker_send_auth_encrypted(havege_state *havege_state, void* socket)
  //@ requires attacker_invariant(?pub, ?pred, ?kc, havege_state, socket, ?attacker);
  //@ ensures  attacker_invariant(pub, pred, kc, havege_state, socket, attacker);
{
  int temp;
  int size1;
  int size2;
  char buffer1[MAX_MESSAGE_SIZE];
  char buffer2[MAX_MESSAGE_SIZE];
  char buffer3[MAX_MESSAGE_SIZE];
  gcm_context gcm_context;
  char iv[16];

  //@ open attacker_invariant(pub, pred, kc, havege_state, socket, attacker);

  size1 = net_recv(socket, buffer1, MAX_MESSAGE_SIZE);
  size2 = net_recv(socket, buffer2, MAX_MESSAGE_SIZE);
  if (size1 <= 0 || size2 <= 16 || size2 > MAX_MESSAGE_SIZE - 16 ||
      (size1 != 16 && size1 != 24 && size1 != 32))
  {
    //@ close attacker_invariant(pub, pred, kc, havege_state, socket, attacker);
    return;
  }
  //@ assert chars(buffer1, size1, ?cs1);
  //@ assert chars(buffer2, size2, ?cs2);

  //@ close gcm_context(&gcm_context);
  //@ interpret_symmetric_key(buffer1, size1);
  //@ assert cryptogram(buffer1, size1, cs_to_ccs(cs1), ?cg_key);
  //@ assert cg_key == cg_symmetric_key(?p, ?c);
  if (gcm_init(&gcm_context, MBEDTLS_CIPHER_ID_AES,
      buffer1, (unsigned int) size1 * 8) == 0)
  {
    if (get_iv(havege_state, iv) == 0)
    {
      //@ chars_to_crypto_chars(buffer2, size2);
      //@ chars__split(buffer3, 16);
      if (gcm_crypt_and_tag(&gcm_context, GCM_ENCRYPT,
                            (unsigned int) size2, iv, 16, NULL, 0,
                            buffer2, (void*) buffer3 + 16, 16, buffer3) == 0)
      {
        /*@
          {
            crypto_chars_to_chars(buffer2, size2);
            public_chars(buffer2, size2);
            chars_to_crypto_chars(buffer2, size2);
            assert exists(?cg_enc);
            assert is_public_auth_encryption_is_public(?proof2, pub, pred);
            proof2(cg_enc);
            assert crypto_chars(secret, buffer3, 16, ?ccs_tag);
            assert crypto_chars(secret, (void*) buffer3 + 16, size2, ?ccs_enc);
            public_cg_ccs(cg_enc);
            public_ccs_split(append(ccs_tag, ccs_enc), 16);
            take_append(16, ccs_tag, ccs_enc);
            drop_append(16, ccs_tag, ccs_enc);
            public_crypto_chars(buffer3, 16);
            public_crypto_chars((void*) buffer3 + 16, size2);
          }
        @*/
        net_send(socket, buffer3, (unsigned int) size2 + 16);
        //@ chars_to_crypto_chars(buffer3, 16);
        //@ chars_to_crypto_chars((void*) buffer3 + 16, size2);
      }
      //@ crypto_chars_to_chars(buffer2, size2);
      //@ crypto_chars_join(buffer3);
      //@ crypto_chars_to_chars(buffer3, size2 + 16);
      //@ crypto_chars_to_chars(iv, 16);
    }
    gcm_free(&gcm_context);
  }
  //@ open gcm_context(&gcm_context);
  //@ close attacker_invariant(pub, pred, kc, havege_state, socket, attacker);
  //@ public_cryptogram(buffer1, cg_key);
}

void attacker_send_auth_decrypted(havege_state *havege_state, void* socket)
  //@ requires attacker_invariant(?pub, ?pred, ?kc, havege_state, socket, ?attacker);
  //@ ensures  attacker_invariant(pub, pred, kc, havege_state, socket, attacker);
{
  int temp;
  int size1;
  int size2;
  char buffer1[MAX_MESSAGE_SIZE];
  char buffer2[MAX_MESSAGE_SIZE];
  char buffer3[MAX_MESSAGE_SIZE];
  gcm_context gcm_context;
  char iv[16];

  //@ open attacker_invariant(pub, pred, kc, havege_state, socket, attacker);

  size1 = net_recv(socket, buffer1, MAX_MESSAGE_SIZE);
  size2 = net_recv(socket, buffer2, MAX_MESSAGE_SIZE);
  if (size1 <= 16 || size2 <= 16 ||
      (size1 != 16 && size1 != 24 && size1 != 32))
  {
    //@ close attacker_invariant(pub, pred, kc, havege_state, socket, attacker);
    return;
  }

  //@ close gcm_context(&gcm_context);
  //@ interpret_symmetric_key(buffer1, size1);
  //@ assert cryptogram(buffer1, size1, ?ccs1, ?cg_key);
  //@ assert cg_key == cg_symmetric_key(?p, ?c);
  if (gcm_init(&gcm_context, MBEDTLS_CIPHER_ID_AES,
      buffer1, (unsigned int) size1 * 8) == 0)
  {
    if (get_iv(havege_state, iv) == 0)
    {
      //@ assert crypto_chars(normal, iv, 16, ?ccs_iv);
      //@ assert chars(buffer2, size2, ?cs2);
      //@ interpret_auth_encrypted(buffer2, size2);
      //@ open cryptogram(buffer2, size2, ?ccs2, ?cg_enc);
      //@ cs_to_ccs_crypto_chars(buffer2, cs2);
      //@ chars_to_crypto_chars(buffer2, size2);
      //@ close exists(cg_enc);
      //@ assert cg_enc == cg_aes_auth_encrypted(?p2, ?c2, ?ccs_output2, ?ccs_iv2);
      //@ crypto_chars_split(buffer2, 16);
      if (gcm_auth_decrypt(&gcm_context, (unsigned int) size2 - 16,
                            iv, 16, NULL, 0, buffer2, 16,
                            (void*) buffer2 + 16, buffer3) == 0)
      {
        /*@ if (!col)
            {
              assert crypto_chars(secret, buffer3, size2 - 16, ?ccs_output);
              ccs_output == ccs_output2;
              ccs_iv == ccs_iv2;
              assert ccs2 == ccs_for_cg(cg_enc);
              assert [_]pub(cg_enc);
              assert is_public_auth_decryption_is_public(?proof3, pub, pred);
              proof3(cg_key, cg_enc);
              public_crypto_chars(buffer3, size2 - 16);
              chars_to_crypto_chars(buffer3, size2 - 16);
            }
        @*/
        zeroize(iv, 16);
        //@ chars_to_crypto_chars(iv, 16);
      }
      //@ crypto_chars_to_chars(buffer3, size2 - 16);
      net_send(socket, buffer3, (unsigned int) size2 - 16);
      //@ crypto_chars_to_chars(buffer2, 16);
      //@ crypto_chars_to_chars((void*) buffer2 + 16, size2 - 16);
      //@ chars_join(buffer2);
      //@ crypto_chars_to_chars(iv, 16);
    }
    gcm_free(&gcm_context);
  }
  //@ open gcm_context(&gcm_context);
  //@ close attacker_invariant(pub, pred, kc, havege_state, socket, attacker);
  //@ public_cryptogram(buffer1, cg_key);
}

void attacker_send_asym_encrypted(havege_state *havege_state, void* socket)
  //@ requires attacker_invariant(?pub, ?pred, ?kc, havege_state, socket, ?attacker);
  //@ ensures  attacker_invariant(pub, pred, kc, havege_state, socket, attacker);
{
  int temp;
  int size1;
  int size2;
  size_t osize;
  char buffer1[MAX_MESSAGE_SIZE];
  char buffer2[MAX_MESSAGE_SIZE];
  char buffer3[MAX_MESSAGE_SIZE];
  pk_context context;

  //@ open attacker_invariant(pub, pred, kc, havege_state, socket, attacker);

  size1 = net_recv(socket, buffer1, MAX_MESSAGE_SIZE);
  size2 = net_recv(socket, buffer2, MAX_MESSAGE_SIZE);
  if (size1 <= 0 || size2 < MINIMAL_STRING_SIZE)
  {
    //@ close attacker_invariant(pub, pred, kc, havege_state, socket, attacker);
    return;
  }

  //@ close pk_context(&context);
  pk_init(&context);
  //@ interpret_public_key(buffer1, size1);
  //@ assert cryptogram(buffer1, size1, ?ccs1, ?cg_key);
  //@ assert cg_key == cg_rsa_public_key(?p, ?c);
  if (pk_parse_public_key(&context, buffer1, (unsigned int) size1) == 0)
  {
    if (size2 * 8 <= size1)
    {
      //@ close random_state_predicate(havege_state_initialized);
      /*@ produce_function_pointer_chunk random_function(
                    attacker_key_item_havege_random_stub)
                  (havege_state_initialized)(state, out, len) { call(); } @*/
      //@ chars_to_crypto_chars(buffer2, size2);
      if (pk_encrypt(&context, buffer2, (unsigned int) size2,
                    buffer3, &osize, MAX_MESSAGE_SIZE,
                    attacker_key_item_havege_random_stub, havege_state) == 0)
      {
        //@ assert osize |-> ?osize_val;
        /*@
          {
            assert cryptogram(buffer3, osize_val, ?ccs_enc, ?cg_enc);
            assert cg_enc == cg_rsa_encrypted(p, c, ?cs2, _);
            assert is_public_asym_encryption_is_public(?proof, pub, pred);
            crypto_chars_to_chars(buffer2, size2);
            public_chars(buffer2, size2);
            proof(cg_enc);
            assert [_]pub(cg_enc);
            public_cryptogram(buffer3, cg_enc);
            chars_to_crypto_chars(buffer2, size2);
          }
        @*/
        net_send(socket, buffer3, osize);
        //@ chars_join(buffer3);
      }
      //@ crypto_chars_to_chars(buffer2, size2);
    }
    //@ pk_release_context_with_key(&context);
  }
  pk_free(&context);
  //@ open pk_context(&context);
  //@ close attacker_invariant(pub, pred, kc, havege_state, socket, attacker);
  //@ public_cryptogram(buffer1, cg_key);
}

void attacker_send_asym_decrypted(havege_state *havege_state, void* socket)
  //@ requires attacker_invariant(?pub, ?pred, ?kc, havege_state, socket, ?attacker);
  //@ ensures  attacker_invariant(pub, pred, kc, havege_state, socket, attacker);
{
  int temp;
  int size1;
  int size2;
  size_t osize;
  char buffer1[MAX_MESSAGE_SIZE];
  char buffer2[MAX_MESSAGE_SIZE];
  char buffer3[MAX_MESSAGE_SIZE];
  pk_context context;

  //@ open attacker_invariant(pub, pred, kc, havege_state, socket, attacker);

  size1 = net_recv(socket, buffer1, MAX_MESSAGE_SIZE);
  size2 = net_recv(socket, buffer2, MAX_MESSAGE_SIZE);
  if (size1 <= 0 || size2 < MINIMAL_STRING_SIZE)
  {
    //@ close attacker_invariant(pub, pred, kc, havege_state, socket, attacker);
    return;
  }
  //@ close pk_context(&context);
  pk_init(&context);
  //@ interpret_private_key(buffer1, size1);
  //@ assert cryptogram(buffer1, size1, ?ccs1, ?cg_key);
  //@ assert cg_key == cg_rsa_private_key(?p, ?c);
  if (pk_parse_key(&context, buffer1, (unsigned int) size1, NULL, 0) == 0)
  {
    if (size2 * 8 <= size1)
    {
      //@ close random_state_predicate(havege_state_initialized);
      /*@ produce_function_pointer_chunk random_function(
                    attacker_key_item_havege_random_stub)
                  (havege_state_initialized)(state, out, len) { call(); } @*/
      //@ interpret_asym_encrypted(buffer2, size2);
      //@ assert cryptogram(buffer2, size2, ?ccs2, ?cg_enc);
      //@ assert cg_enc == cg_rsa_encrypted(?p2, ?c2, ?ccs_output2, ?ent);
      //@ structure s = known_value(0, nil);
      //@ close decryption_pre(false, false, attacker, s, ccs2);
      int success = pk_decrypt(&context, buffer2, (unsigned int) size2,
                               buffer3, &osize, MAX_MESSAGE_SIZE,
                               attacker_key_item_havege_random_stub,
                               havege_state);
      //@ open decryption_post(false, ?garbage, attacker, s, p, c, ?ccs_output);
      //@ assert crypto_chars(?kind, buffer3, ?osize_val, ccs_output);
      /*@ if (garbage)
          {
            assert is_public_key_classifier(?proof, _, _, _);
            proof(cg_key, p, c, false);
            decryption_garbage(buffer3, osize_val, s);
          }
          else if (success == 0)
          {
            assert [_]pub(cg_enc);
            assert is_public_asym_decryption_is_public(?proof, pub, pred);
            proof(cg_key, cg_enc);
            public_crypto_chars(buffer3, osize_val);
            chars_to_crypto_chars(buffer3, osize_val);
          }
      @*/
      //@ crypto_chars_to_chars(buffer3, osize_val);
      if (success == 0) net_send(socket, buffer3, osize);
      //@ chars_chars__join(buffer3);
      //@ open cryptogram(buffer2, size2, ccs2, cg_enc);
      //@ public_crypto_chars(buffer2, size2);
    }
    //@ pk_release_context_with_key(&context);
  }
  pk_free(&context);
  //@ open pk_context(&context);
  //@ close attacker_invariant(pub, pred, kc, havege_state, socket, attacker);
  //@ public_cryptogram(buffer1, cg_key);
}

void attacker_send_asym_signature(havege_state *havege_state, void* socket)
  //@ requires attacker_invariant(?pub, ?pred, ?kc, havege_state, socket, ?attacker);
  //@ ensures  attacker_invariant(pub, pred, kc, havege_state, socket, attacker);
{
  int temp;
  int size1;
  int size2;
  size_t osize;
  char buffer1[MAX_MESSAGE_SIZE];
  char buffer2[MAX_MESSAGE_SIZE];
  char buffer3[MAX_MESSAGE_SIZE];
  pk_context context;

  //@ open attacker_invariant(pub, pred, kc, havege_state, socket, attacker);

  size1 = net_recv(socket, buffer1, MAX_MESSAGE_SIZE);
  size2 = net_recv(socket, buffer2, MAX_MESSAGE_SIZE);
  if (size1 <= 0 || size2 < MINIMAL_STRING_SIZE)
  {
    //@ close attacker_invariant(pub, pred, kc, havege_state, socket, attacker);
    return;
  }

  //@ close pk_context(&context);
  pk_init(&context);
  //@ interpret_private_key(buffer1, size1);
  //@ assert cryptogram(buffer1, size1, ?ccs1, ?cg_key);
  //@ assert cg_key == cg_rsa_private_key(?p, ?c);
  if (pk_parse_key(&context, buffer1, (unsigned int) size1, NULL, 0) == 0)
  {
    if (size2 * 8 < size1)
    {
      //@ close random_state_predicate(havege_state_initialized);
      /*@ produce_function_pointer_chunk random_function(
                  attacker_key_item_havege_random_stub)
                  (havege_state_initialized)(state, out, len) { call(); } @*/
      //@ chars_to_crypto_chars(buffer2, size2);
      if (pk_sign(&context, MBEDTLS_MD_NONE, buffer2, (unsigned int) size2,
                  buffer3, &osize, attacker_key_item_havege_random_stub,
                  havege_state) == 0)
      {
        /*@
          {
            assert osize |-> ?osize_val;
            assert cryptogram(buffer3, osize_val, ?ccs_enc, ?cg_sig);
            assert cg_sig == cg_rsa_signature(p, c, ?cs2, _);
            assert is_public_asym_signature_is_public(?proof, pub, pred);
            crypto_chars_to_chars(buffer2, size2);
            public_chars(buffer2, size2);
            proof(cg_sig);
            public_cryptogram(buffer3, cg_sig);
            chars_to_crypto_chars(buffer2, size2);
          }
        @*/
        net_send(socket, buffer3, osize);
      }
      //@ crypto_chars_to_chars(buffer2, size2);
    }
    //@ pk_release_context_with_key(&context);
  }
  pk_free(&context);
  //@ open pk_context(&context);
  //@ close attacker_invariant(pub, pred, kc, havege_state, socket, attacker);
  //@ public_cryptogram(buffer1, cg_key);
}

void attacker_core(havege_state *havege_state, void* socket)
  //@ requires attacker_invariant(?pub, ?pred, ?kc, havege_state, socket, ?attacker);
  //@ ensures  attacker_invariant(pub, pred, kc, havege_state, socket, attacker);
{
  int action;
  //@ open attacker_invariant(pub, pred, kc, havege_state, socket, attacker);
  //@ close_havege_util(pub, pred, attacker);
  r_int(havege_state, &action);
  //@ open_havege_util(pub, pred, attacker);
  //@ close attacker_invariant(pub, pred, kc, havege_state, socket, attacker);

  switch (action % 14)
  {
    case 0:
      attacker_send_data(havege_state, socket);
      break;
    case 1:
      attacker_send_concatenation(havege_state, socket);
      break;
    case 2:
      attacker_send_split(havege_state, socket);
      break;
    case 3:
      attacker_send_random(havege_state, socket);
      break;
    case 4:
      attacker_send_keys(havege_state, socket);
      break;
    case 5:
      attacker_send_hash(havege_state, socket);
      break;
    case 6:
      attacker_send_hmac(havege_state, socket);
      break;
    case 7:
      attacker_send_encrypted(havege_state, socket);
      break;
    case 8:
      attacker_send_decrypted(havege_state, socket);
      break;
    case 9:
      attacker_send_auth_encrypted(havege_state, socket);
      break;
    case 10:
      attacker_send_auth_decrypted(havege_state, socket);
      break;
    case 11:
      attacker_send_asym_encrypted(havege_state, socket);
      break;
    case 12:
      attacker_send_asym_decrypted(havege_state, socket);
      break;
    case 13:
      attacker_send_asym_signature(havege_state, socket);
      break;
  }
}

void attacker()
  /*@ requires [_]public_invar(?pub) &*&
               [_]decryption_key_classifier(?classifier) &*&
               public_invariant_constraints(pub, ?proof_pred) &*&
               proof_pred() &*& principal(?bad_one, _) &*& true == bad(bad_one) &*&
               is_public_key_classifier(_, pub, classifier, proof_pred); @*/
  /*@ ensures  public_invariant_constraints(pub, proof_pred) &*&
               proof_pred() &*& principal(bad_one, _) &*&
               is_public_key_classifier(_, pub, classifier, proof_pred); @*/
{
  bool havege_failure = false;
  int server_or_client;
  int port;
  int* socket;
  int socket1;
  int socket2;
  //@ open principal(bad_one, _);

  havege_state havege_state;
  //@ close havege_state(&havege_state);
  havege_init(&havege_state);

  //@ open public_invariant_constraints(pub, proof_pred);
  /*@
  {
    lemma void principal_with_public_nonces(cryptogram nonce)
      requires  is_bad_nonce_is_public(?proof, pub, proof_pred) &*&
                proof_pred() &*&
                nonce == cg_nonce(bad_one, _);
      ensures   is_bad_nonce_is_public(proof, pub, proof_pred) &*&
                proof_pred() &*&
                [_]pub(nonce);
    {
      proof(nonce);
    }
    produce_lemma_function_pointer_chunk(principal_with_public_nonces) :
      principal_with_public_nonces
        (pub, attacker_nonce_pred(pub, proof_pred), bad_one)(nonce__)
        {
          open attacker_nonce_pred(pub, proof_pred)();
          call();
          close attacker_nonce_pred(pub, proof_pred)();
        }
    {duplicate_lemma_function_pointer_chunk(principal_with_public_nonces);};
  }
  @*/
  //@ close_havege_util(pub, proof_pred, bad_one);
  r_int(&havege_state, &server_or_client);
  r_int(&havege_state, &port);
  //@ open_havege_util(pub, proof_pred, bad_one);

  bool network_failure = false;

  if (server_or_client % 2 == 0)
  {
    if(net_connect(&socket1, NULL, port) != 0) network_failure = true;
    else if(net_set_block(socket1) != 0) network_failure = true;
    socket = &socket1;
  }
  else
  {
    if(net_bind(&socket1, NULL, port) != 0)
      {network_failure = true;}
    else if(net_accept(socket1, &socket2, NULL) != 0)
      {net_close(socket1); network_failure = true;}
    else if(net_set_block(socket2) != 0)
      {net_close(socket1); network_failure = true;}
    socket = &socket2;
  }

  if (!network_failure)
  {
    //@ close attacker_invariant(pub, proof_pred, ?kc, &havege_state, socket, bad_one);
    int j = 0;
    while(j < ATTACKER_ITERATIONS)
      /*@ invariant attacker_invariant(pub, proof_pred, kc,
                                       &havege_state, socket, bad_one); @*/
    {
      attacker_core(&havege_state, socket);
      j++;
    }
    //@ open attacker_invariant(pub, proof_pred, kc, &havege_state, socket, bad_one);

    if (server_or_client % 2 == 0)
      net_close(socket1);
    else
    {
      net_close(socket1);
      net_close(socket2);
    }
  }

  //@ close public_invariant_constraints(pub, proof_pred);
  //@ close principal(bad_one, _);
  havege_free(&havege_state);
  //@ open havege_state(&havege_state);
  /*@ leak is_principal_with_public_nonces(_, pub,
                            attacker_nonce_pred(pub, proof_pred), bad_one); @*/
}
