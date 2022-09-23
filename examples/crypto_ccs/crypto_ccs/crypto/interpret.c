//@ #include "interpret.gh"
//@ #include "public_chars.gh"

/*@

#define GENERAL_INTERPRET_METHOD_IMPL(KIND, TAG, CG) \
lemma void interpret_##KIND(char *buffer, int size) \
  requires [_]public_invar(?pub) &*& \
           [?f]chars(buffer, size, ?cs); \
  ensures  [f]cryptogram(buffer, size, ?ccs, ?cg) &*& [_]pub(cg) &*& \
           ccs == cs_to_ccs(cs) &*& cg == CG &*& \
           [_]public_ccs(ccs); \
{ \
  list<crypto_char> ccs = cs_to_ccs(cs); \
  cryptogram key = ccs_for_cg_sur(ccs, TAG); \
  assert key == CG; \
  public_cs(cs); \
  public_ccs_cg(key); \
  chars_to_secret_crypto_chars(buffer, size); \
  close [f]cryptogram(buffer, size, ccs, key); \
}

GENERAL_INTERPRET_METHOD_IMPL(nonce,          tag_nonce,          cg_nonce(_,_))
GENERAL_INTERPRET_METHOD_IMPL(symmetric_key,  tag_symmetric_key,  cg_symmetric_key(_, _))
GENERAL_INTERPRET_METHOD_IMPL(public_key,     tag_public_key,     cg_rsa_public_key(_, _))
GENERAL_INTERPRET_METHOD_IMPL(private_key,    tag_private_key,    cg_rsa_private_key(_, _))
GENERAL_INTERPRET_METHOD_IMPL(hash,           tag_hash,           cg_sha512_hash(_))
GENERAL_INTERPRET_METHOD_IMPL(hmac,           tag_hmac,           cg_sha512_hmac(_, _, _))
GENERAL_INTERPRET_METHOD_IMPL(encrypted,      tag_encrypted,      cg_aes_encrypted(_, _, _, _))
GENERAL_INTERPRET_METHOD_IMPL(auth_encrypted, tag_auth_encrypted, cg_aes_auth_encrypted(_, _, _, _))
GENERAL_INTERPRET_METHOD_IMPL(asym_encrypted, tag_asym_encrypted, cg_rsa_encrypted(_, _, _, _))                              
GENERAL_INTERPRET_METHOD_IMPL(asym_signature, tag_asym_signature, cg_rsa_signature(_, _, _, _))                              
                              











                              

@*/