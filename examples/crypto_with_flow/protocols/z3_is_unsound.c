#include <stdlib.h>
#include <string.h>
#include <stdio.h>
//@ #include "quantifiers.gh"

#include "../../annotated_api/polarssl_definitions/polarssl_definitions.h"

#define NONCE_SIZE 8
#define KEY_SIZE 128

#define SERVER_PORT 50000

//@ import_module public_invariant_mod;
//@ import_module principals_mod;

/*@

predicate z3_proof_pred() = 
  exists(?attacker) &*& true == bad(attacker)
;

predicate z3_pub_(int sender, cryptogram r_nonce) = true;

predicate z3_pub(cryptogram cg) =
  switch (cg)
  {
    case cg_random(p0, c0):
      return true == bad(p0);
    case cg_symmetric_key(p0, c0):
      return true == bad(p0);
    case cg_public_key(p0, c0):
      return true;
    case cg_private_key(p0, c0):
      return true == bad(p0);
    case cg_hash(cs0):
      return true;
    case cg_hmac(p0, c0, cs0):
      return true == bad(p0) &*& [_]public_generated(z3_pub)(cs0);
    case cg_encrypted(p0, c0, cs0, ent0):
      return true == bad(p0) &*& [_]public_generated(z3_pub)(cs0);
    case cg_auth_encrypted(p0, c0, mac0, cs0, ent0):
      return true == bad(p0) &*& [_]public_generated(z3_pub)(cs0);
    case cg_asym_encrypted(p0, c0, cs0, ent0):
      return [_]z3_pub_(?p1, ?r_nonce) &*& bad(p0) || bad(p1) ?
        [_]public_generated(z3_pub)(cs0)
      :
        cs0 == chars_for_cg(r_nonce);
    case cg_asym_signature(p0, c0, cs0, ent0):
      return true == bad(p0);
  }
;

DEFAULT_IS_PUBLIC_RANDOM(z3)
DEFAULT_IS_PUBLIC_KEY(z3)
DEFAULT_IS_PUBLIC_PUBLIC_KEY(z3)
DEFAULT_IS_PUBLIC_PRIVATE_KEY(z3)
DEFAULT_IS_PUBLIC_HASH(z3)
DEFAULT_IS_PUBLIC_HMAC(z3)
DEFAULT_IS_PUBLIC_ENCRYPTED(z3)
DEFAULT_IS_PUBLIC_DECRYPTED(z3)
DEFAULT_IS_PUBLIC_AUTH_ENCRYPTED(z3)
DEFAULT_IS_PUBLIC_AUTH_DECRYPTED(z3)
// DEFAULT_IS_PUBLIC_ASYMMETRIC_ENCRYPTED(z3)
// DEFAULT_IS_PUBLIC_ASYMMETRIC_DECRYPTED(z3)
DEFAULT_IS_PUBLIC_ASYMMETRIC_SIGNATURE(z3)

lemma void public_asym_encryption_is_public(cryptogram encrypted)
  requires z3_proof_pred() &*&
           encrypted == cg_asym_encrypted(?p, ?c, ?pay, ?ent) &*&
           [_]z3_pub(cg_public_key(p, c)) &*&
           [_]public_generated(z3_pub)(pay);
  ensures  z3_proof_pred() &*&
           [_]z3_pub(encrypted);
{
  open  [_]z3_pub(cg_public_key(p, c));
  POLARSSL_SWITCH_1(PREFIX, cg_public_key(p, c));
  open z3_proof_pred();
  assert exists(?attacker);
  close z3_proof_pred();
  close z3_pub_(attacker, encrypted);
  leak z3_pub_(attacker, encrypted);
  close z3_pub(encrypted);
  leak z3_pub(encrypted);
}

lemma void public_asym_decryption_is_public(cryptogram key,
                                            cryptogram encrypted)
  requires key == cg_private_key(?p, ?c) &*&
           encrypted == cg_asym_encrypted(p, c, ?pay, ?ent) &*&
           [_]z3_pub(key) &*&
           [_]z3_pub(encrypted);
  ensures  [_]public_generated(z3_pub)(pay);
{
  open  [_]z3_pub(key);
  open  [_]z3_pub(encrypted);
  
  POLARSSL_SWITCH_1(PREFIX, cg_private_key(p, c));
  assert true == bad(p);
}

@*/

int random_stub_z3(void *havege_state, char *output, size_t len)
  //@ requires PRG_PRECONDITION(havege_state_initialized, havege_state);
  //@ ensures PRG_POSTCONDITION(havege_state_initialized, havege_state);
{
  return havege_random(havege_state, output, len);
}

void crashing_function(pk_context* pub_context, pk_context* priv_context,
                       struct havege_state* state, char* nonce)
  /*@ requires [_]public_invar(z3_pub) &*&
               principal(?principal, _) &*& !bad(principal) &*&
               pk_context_with_key(pub_context, pk_public,
                                   principal, ?count, 8 * KEY_SIZE) &*&
               pk_context_with_key(priv_context, pk_private,
                                   principal, count, 8 * KEY_SIZE) &*&
               havege_state_initialized(state) &*&
               cryptogram(nonce, NONCE_SIZE, ?nonce_cs, ?nonce_cg) &*&
                 nonce_cg == cg_random(principal, _); @*/
  /*@ ensures  principal(principal, _) &*&
               pk_context_with_key(pub_context, pk_public,
                                   principal, count, 8 * KEY_SIZE) &*&
               pk_context_with_key(priv_context, pk_private,
                                   principal, count, 8 * KEY_SIZE) &*&
               havege_state_initialized(state) &*&
               cryptogram(nonce, NONCE_SIZE, nonce_cs, nonce_cg); @*/
{
  int socket1;
  int socket2;
  unsigned int size;
  char message[NONCE_SIZE];
  char encrypted[KEY_SIZE];
  //@ assert chars(encrypted, KEY_SIZE, ?enc_cs);
  
  // Decrypt the message
  //@ close optional_crypto_chars(false, encrypted, KEY_SIZE, enc_cs);
  /*@ produce_function_pointer_chunk random_function(random_stub_z3)
                    (havege_state_initialized)(state_, out, len) { call(); } @*/
  //@ close random_state_predicate(havege_state_initialized);
  if (pk_decrypt(priv_context, encrypted, KEY_SIZE, message, 
                  &size, NONCE_SIZE, random_stub_z3, state) != 0)
    abort();
  if (size != NONCE_SIZE)
    abort();
  //@ open optional_crypto_chars(false, encrypted, KEY_SIZE, enc_cs);
  //@ assert u_integer(&size, NONCE_SIZE);
  //@ assert optional_crypto_chars(!collision_in_run, message, NONCE_SIZE, ?dec_cs);
  //@ cryptogram enc_cg;
  /*@ if (!collision_in_run)
      {
        assert [_]exists(?ent);
        enc_cg = cg_asym_encrypted(principal, count, dec_cs, ent);
        assert enc_cs == chars_for_cg(enc_cg);
        public_chars_extract(encrypted, enc_cg);
      }
  @*/
  
  // Interpret the message
  //@ close optional_crypto_chars(!collision_in_run, (void*) message, NONCE_SIZE, _);
  //@ close optional_crypto_chars(!collision_in_run, nonce, NONCE_SIZE, nonce_cs);
  if (memcmp((void*) message, nonce, NONCE_SIZE) != 0) abort();
  
  /*@ if (!collision_in_run && !bad(principal))
      {
        open [_]z3_pub(enc_cg);
        assert [_]z3_pub_(?sender, ?nonce_cg2);
        if (bad(sender))
        {
          public_crypto_chars(nonce, NONCE_SIZE, nonce_cs);
          public_chars_extract(nonce, nonce_cg);
          open [_]z3_pub(nonce_cg);
          assert false;
        }
        
        //UNSOUND!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
        //
        //*This should not be true in case of a collision, otherwise false can
        // be proven.
        //
        //*Cannot trigger this unsoundness because contracts were developped in
        // sush a way that a collision can only be proven in exhaustive search.
        //
        //*How does z3 prover this?
        assert nonce_cg == nonce_cg2;
      }
  @*/
  zeroize(message, NONCE_SIZE);
  //@ close cryptogram(nonce, NONCE_SIZE, nonce_cs, nonce_cg);
}

int main(int argc, char **argv) //@ : main_full(z3_is_unsound)
    //@ requires module(z3_is_unsound, true);
    //@ ensures true;
{
  //@ open_module();
  //@ PUBLIC_INVARIANT_CONSTRAINTS(z3)
  //@ public_invariant_init(z3_pub);
  //@ principals_init();
  //@ int principal = principal_create();
  //@ assume (!bad(principal));
  
  havege_state havege_state;
  pk_context context;
  pk_context pub_context;
  pk_context priv_context;
  char priv_key[4096];
  char pub_key[4096];
  
  //@ close havege_state(&havege_state);
  havege_init(&havege_state);
  
  //@ close random_state_predicate(havege_state_initialized);
  /*@ produce_function_pointer_chunk random_function(random_stub_z3)
                    (havege_state_initialized)(state, out, len) { call(); } @*/
  //@ close pk_context(&context);
  pk_init(&context);
  if (pk_init_ctx(&context, pk_info_from_type(POLARSSL_PK_RSA)) != 0)
    abort();
  //@ close rsa_key_request(principal, 0);
  if (rsa_gen_key(context.pk_ctx, random_stub_z3, (void*) &havege_state,
                  (unsigned int) 8 * KEY_SIZE, 65537) != 0)
    abort();
  if (pk_write_pubkey_pem(&context, pub_key, 
                          (unsigned int) 8 * KEY_SIZE) != 0) abort();
  if (pk_write_key_pem(&context, priv_key,
                        (unsigned int) 8 * KEY_SIZE) != 0) abort();
  //@ assert cryptogram(priv_key, 8 * KEY_SIZE, ?cs_priv_key, ?cg_priv_key);
  //@ assert cryptogram(pub_key, 8 * KEY_SIZE, ?cs_pub_key, ?cg_pub_key);
  //@ assert cg_priv_key == cg_private_key(principal, 1);
  //@ assert cg_pub_key == cg_public_key(principal, 1);
  //@ pk_release_context_with_keys(&context);
  pk_free(&context);
  //@ open pk_context(&context);
  
  //@ close pk_context(&pub_context);
  pk_init(&pub_context);
  if (pk_parse_public_key(&pub_context, pub_key, 
                          (unsigned int) 8 * KEY_SIZE) != 0)
    abort();
  //@ close pk_context(&priv_context);
  pk_init(&priv_context);
  if (pk_parse_key(&priv_context, priv_key, 
                   (unsigned int) 8 * KEY_SIZE, NULL, 0) != 0)
    abort();
  //@ open cryptogram(priv_key, 8 * KEY_SIZE, cs_priv_key, cg_priv_key);
  //@ close optional_crypto_chars(!collision_in_run, priv_key, 8 * KEY_SIZE, cs_priv_key);
  zeroize(priv_key, 8 * KEY_SIZE);
  //@ close z3_pub(cg_pub_key);
  //@ leak z3_pub(cg_pub_key);
  //@ assert cryptogram(pub_key, 8 * KEY_SIZE, cs_pub_key, cg_pub_key);
  //@ public_cryptogram(pub_key, cg_pub_key);
  //@ assert chars(pub_key, 8 * KEY_SIZE, cs_pub_key);
  
  {
    char nonce[NONCE_SIZE];
    
    //@ close random_request(principal, 0, false);
    if (havege_random(&havege_state, nonce, NONCE_SIZE) != 0) abort();
    
    crashing_function(&pub_context, &priv_context, &havege_state, nonce);
    
    //@ open cryptogram(nonce, NONCE_SIZE, ?cs_nonce, _);
    //@ close optional_crypto_chars(!collision_in_run, nonce, NONCE_SIZE, cs_nonce);
    zeroize(nonce, NONCE_SIZE);
  }
  
  havege_free(&havege_state);
  //@ open havege_state(&havege_state);
  
  //@ pk_release_context_with_key(&pub_context);
  pk_free(&pub_context);
  //@ open pk_context(&pub_context);
  
  //@ pk_release_context_with_key(&priv_context);
  pk_free(&priv_context);
  //@ open pk_context(&priv_context);
  
  //@ principal_destroy(principal);
  //@ principals_exit();
  //@ leak random_state_predicate(havege_state_initialized);
  //@ leak public_invariant_constraints(z3_pub, z3_proof_pred);
  //@ leak module(public_invariant_mod, false);
  return 0;
}
