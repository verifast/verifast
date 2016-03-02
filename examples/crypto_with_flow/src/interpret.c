//@ #include "../annotated_api/general_definitions/interpret.gh"
//@ #include "../annotated_api/general_definitions/public_chars.gh"

/*@

#define GENERAL_INTERPRET_METHOD_IMPL(KIND, TAG, CG) \
lemma void interpret_##KIND(char *buffer, int size) \
  requires [_]public_invar(?pub) &*& \
           [?f]chars(buffer, size, ?cs); \
  ensures  [f]cryptogram(buffer, size, cs, ?cg) &*& [_]pub(cg) &*& \
           cg == CG &*& [_]public_generated(pub)(cs); \
{ \
  cryptogram key = chars_for_cg_sur(cs, TAG); \
  public_chars(buffer, size); \
  public_chars_extract(buffer, key); \
  assert key == CG; \
  public_chars(buffer, size); \
  open [_]public_generated(pub)(cs); \
  if (!col) forall_mem(key, cgs_in_chars(cs), cg_is_generated); \
  chars_to_secret_crypto_chars(buffer, size); \
  close [f]cryptogram(buffer, size, cs, key); \
}

GENERAL_INTERPRET_METHOD_IMPL(nonce,          tag_nonce,          cg_nonce(_,_))
GENERAL_INTERPRET_METHOD_IMPL(symmetric_key,  tag_symmetric_key,  cg_symmetric_key(_, _))
GENERAL_INTERPRET_METHOD_IMPL(public_key,     tag_public_key,     cg_public_key(_, _))
GENERAL_INTERPRET_METHOD_IMPL(private_key,    tag_private_key,    cg_private_key(_, _))
GENERAL_INTERPRET_METHOD_IMPL(hash,           tag_hash,           cg_hash(_))
GENERAL_INTERPRET_METHOD_IMPL(hmac,           tag_hmac,           cg_hmac(_, _, _))
GENERAL_INTERPRET_METHOD_IMPL(encrypted,      tag_encrypted,      cg_encrypted(_, _, _, _))
GENERAL_INTERPRET_METHOD_IMPL(auth_encrypted, tag_auth_encrypted, cg_auth_encrypted(_, _, _, _))
GENERAL_INTERPRET_METHOD_IMPL(asym_encrypted, tag_asym_encrypted, cg_asym_encrypted(_, _, _, _))                              
GENERAL_INTERPRET_METHOD_IMPL(asym_signature, tag_asym_signature, cg_asym_signature(_, _, _, _))                              
                              











                              

@*/