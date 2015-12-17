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
  if (!col)
  {
    dummy_foreach_singleton(pub, cg);
    close_public_generated(cs);
    public_crypto_chars(array, n);
  }
  else
  {
    crypto_chars_to_chars(array, n);
  }
}

lemma void public_chars_extract(char *array, cryptogram cg)
  requires [_]public_invar(?pub) &*&
           [?f]chars(array, ?n, ?cs) &*&
           cs == chars_for_cg(cg);
  ensures  [f]chars(array, n, cs) &*&
           true == cg_is_generated(cg) &*& [_]pub(cg);
{
  public_chars(array, n);
  open [_]public_generated(pub)(cs);
  dummy_foreach_extract(cg, cgs_in_chars(cs));
}

lemma void public_crypto_chars_extract(char *array, cryptogram cg)
  requires [_]public_invar(?pub) &*&
           [?f]crypto_chars(_, array, ?n, ?cs) &*&
           cs == chars_for_cg(cg) &*&
           [_]public_generated(pub)(cs);
  ensures  [f]chars(array, n, cs) &*&
           true == cg_is_generated(cg) &*& [_]pub(cg);
{
  open [_]public_generated(pub)(cs);
  dummy_foreach_extract(cg, cgs_in_chars(cs));
  public_crypto_chars(array, n);
}

lemma void public_cryptogram_extract(char *array)
  requires [_]public_invar(?pub) &*&
           [?f]cryptogram(array, ?n, ?cs, ?cg) &*&
           [_]public_generated(pub)(cs);
  ensures  [f]cryptogram(array, n, cs, cg) &*&
           col ? true : [_]pub(cg);
{
  open [f]cryptogram(array, n, cs, cg);
  if (!col) public_crypto_chars_extract(array, cg);
  if (col) crypto_chars_to_chars(array, n);
  chars_to_secret_crypto_chars(array, n);
  close [f]cryptogram(array, n, cs, cg);
}

lemma void public_generated(predicate(cryptogram) pub,
                            cryptogram cg)
  requires [_]pub(cg) &*& true == cg_is_generated(cg);
  ensures  [_]public_generated(pub)(chars_for_cg(cg));
{
  cg_constraints(cg);
  dummy_foreach_singleton(pub, cg);
  close public_generated(pub)(chars_for_cg(cg));
  leak public_generated(pub)(chars_for_cg(cg));
}

lemma void public_generated_extract(predicate(cryptogram) pub,
                                    list<char> cs, cryptogram cg)
  requires [_]public_generated(pub)(cs) &*&
           mem(cg, cgs_in_chars(cs)) || cs == chars_for_cg(cg);
  ensures  true == cg_is_generated(cg) &*& [_]pub(cg);
{
  open [_]public_generated(pub)(cs);
  forall_mem(cg, cgs_in_chars(cs), cg_is_generated);
  dummy_foreach_extract(cg, cgs_in_chars(cs));
}

lemma void public_generated_split(predicate(cryptogram) pub,
                                  list<char> cs, int i)
  requires 0 <= i && i <= length(cs) &*&
           [_]public_generated(pub)(cs);
  ensures  [_]public_generated(pub)(take(i, cs)) &*&
           [_]public_generated(pub)(drop(i, cs));
{
  open [_]public_generated(pub)(cs);
  list<char> cs1 = take(i, cs);
  list<char> cs2 = drop(i, cs);
  list<cryptogram> cgs = cgs_in_chars(cs);
  list<cryptogram> cgs1 = cgs_in_chars(cs1);
  list<cryptogram> cgs2 = cgs_in_chars(cs2);
  cgs_in_chars_upper_bound_split(cs, cgs, i);
  cgs_in_chars_upper_bound_superset(take(i, cs), cgs1, cgs);
  cgs_in_chars_upper_bound_superset(drop(i, cs), cgs2, cgs);
  dummy_foreach_subset(cgs1, cgs);
  forall_subset(cgs1, cgs, cg_is_generated);
  dummy_foreach_subset(cgs2, cgs);
  forall_subset(cgs2, cgs, cg_is_generated);
  close public_generated(pub)(cs1);
  leak  public_generated(pub)(cs1);
  close public_generated(pub)(cs2);
  leak  public_generated(pub)(cs2);
}

lemma void public_generated_join(predicate(cryptogram) pub,
                                 list<char> cs1, list<char> cs2)
  requires [_]public_generated(pub)(cs1) &*&
           [_]public_generated(pub)(cs2);
  ensures  [_]public_generated(pub)(append(cs1, cs2));
{
  open [_]public_generated(pub)(cs1);
  open [_]public_generated(pub)(cs2);
  list<char> cs3 = append(cs1, cs2);
  list<cryptogram> cgs1 = cgs_in_chars(cs1);
  list<cryptogram> cgs2 = cgs_in_chars(cs2);
  list<cryptogram> cgs3 = cgs_in_chars(cs3);
  cgs_in_chars_upper_bound_(cs1);
  cgs_in_chars_upper_bound_(cs2);
  cgs_in_chars_upper_bound_join(cs1, cgs1, cs2, cgs2);
  assert true == subset(cgs3, union(cgs1, cgs2));
  dummy_foreach_union(cgs1, cgs2);
  dummy_foreach_subset(cgs_in_chars(cs3), union(cgs1, cgs2));
  forall_union(cgs1, cgs2, cg_is_generated);
  forall_subset(cgs3, union(cgs1, cgs2), 
                cg_is_generated);
  close public_generated(pub)(cs3);
  leak public_generated(pub)(cs3);
}

@*/