//@ #include "../annotated_api/general_definitions/public_chars.gh"
//@ #include "../annotated_api/general_definitions/cryptogram_bounds.gh"

/*@

lemma void close_public_generated(list<char> cs)
  requires [_]public_invar(?pub) &*&
           [_]dummy_foreach(cgs_in_chars(cs), pub) &*&
           true == forall(cgs_in_chars(cs), cg_is_generated);
  ensures  [_]public_generated(pub)(cs);
{
  close public_generated(pub)(cs);
  leak public_generated(pub)(cs);
}

lemma void public_cryptogram(char *array, cryptogram cg)
  requires [_]public_invar(?pub) &*&
           [?f]cryptogram(array, ?n, ?cs, cg) &*&
           [_]pub(cg);
  ensures  [f]chars(array, n, cs);
{
  open [f]cryptogram(array, n, cs, cg);
  if (!collision_in_run)
  {
    dummy_foreach_singleton(pub, cg);
    close_public_generated(cs);
    public_crypto_chars(array, n, cs);
  }
}

lemma void public_chars_extract(char *array, cryptogram cg)
  requires [_]public_invar(?pub) &*&
           [?f]chars(array, ?n, ?cs) &*&
           cs == chars_for_cg(cg);
  ensures  [f]chars(array, n, cs) &*&
           true == cg_is_generated(cg) &*& [_]pub(cg);
{
  public_chars(array, n, cs);
  open [_]public_generated(pub)(cs);
  dummy_foreach_extract(cg, cgs_in_chars(cs));
}

lemma void public_crypto_chars_extract(char *array, cryptogram cg)
  requires [_]public_invar(?pub) &*&
           [?f]crypto_chars(array, ?n, ?cs) &*&
           cs == chars_for_cg(cg) &*&
           [_]public_generated(pub)(cs);
  ensures  [f]crypto_chars(array, n, cs) &*&
           true == cg_is_generated(cg) &*& [_]pub(cg);
{
  open [_]public_generated(pub)(cs);
  dummy_foreach_extract(cg, cgs_in_chars(cs));
}

lemma void public_cryptogram_extract(char *array)
  requires [_]public_invar(?pub) &*&
           [?f]cryptogram(array, ?n, ?cs, ?cg) &*&
           [_]public_generated(pub)(cs);
  ensures  [f]cryptogram(array, n, cs, cg) &*&
           collision_in_run ? true : [_]pub(cg);
{
  open [f]cryptogram(array, n, cs, cg);
  if (!collision_in_run) 
  {
    public_crypto_chars_extract(array, cg);
  }
  close [f]cryptogram(array, n, cs, cg);
}

@*/