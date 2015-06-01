//@ #include "../annotated_api/general_definitions/key_util.gh"
//@ #include "../annotated_api/general_definitions/public_chars.gh"

/*@

#define GENERAL_INTERPRET_METHOD(SC_KIND, BC_KIND) \
lemma void interpret_##SC_KIND##_key(char *buffer, int size, list<char> cs) \
  requires [_]public_invar(?pub) &*& \
           [?f]chars(buffer, size, cs); \
  ensures  [f]cryptogram(buffer, size, cs, ?cg) &*& [_]pub(cg) &*& \
           cg == cg_##SC_KIND##_key(?p, ?c); \
{ \
  cryptogram key = chars_for_cg_sur(cs, CG_##BC_KIND##_KEY_TAG); \
  public_chars_extract(buffer, key); \
  assert key == cg_##SC_KIND##_key(?p, ?c); \
  public_chars(buffer, size, cs); \
  open [_]public_generated(pub)(cs); \
  crypto_chars(buffer, size, cs); \
  forall_mem(key, cgs_in_chars(cs), cg_is_generated); \
  close [f]cryptogram(buffer, size, cs, key); \
}

GENERAL_INTERPRET_METHOD(symmetric, SYMMETRIC)

GENERAL_INTERPRET_METHOD(public, PUBLIC)

GENERAL_INTERPRET_METHOD(private, PRIVATE)

@*/