//@ #include "../annotated_api/general_definitions/public_chars.gh"
//@ #include "../annotated_api/general_definitions/cryptogram_bounds.gh"

/*@

lemma void close_public_generated(list<crypto_char> ccs)
  requires [_]public_invar(?pub) &*&
           [_]dummy_foreach(cgs_in_ccs(ccs), pub) &*&
           true == forall(cgs_in_ccs(ccs), cg_is_generated);
  ensures  [_]public_generated(pub)(ccs);
{
  close public_generated(pub)(ccs);
  leak public_generated(pub)(ccs);
}

lemma void public_cryptogram(char *array, cryptogram cg)
  requires [_]public_invar(?pub) &*&
           [?f]cryptogram(array, ?n, ?ccs, cg) &*&
           [_]pub(cg);
  ensures  [f]chars(array, n, ?cs) &*& 
           [_]public_generated(pub)(ccs) &*&
           ccs == cs_to_ccs(cs);
{
  open [f]cryptogram(array, n, ccs, cg);
  if (!col)
  {
    dummy_foreach_singleton(pub, cg);
    close_public_generated(ccs);
    public_crypto_chars(array, n);
  }
  else
  {
    crypto_chars_to_chars(array, n);
    public_chars(array, n);
  }
}

lemma void public_chars_extract(char *array, cryptogram cg)
  requires [_]public_invar(?pub) &*&
           [?f]chars(array, ?n, ?cs) &*&
           ccs_for_cg(cg) == cs_to_ccs(cs);
  ensures  [f]chars(array, n, cs) &*&
           true == cg_is_generated(cg) &*& [_]pub(cg);
{
  public_chars(array, n);
  open [_]public_generated(pub)(?ccs);
  dummy_foreach_extract(cg, cgs_in_ccs(ccs));
}

lemma void public_crypto_chars_extract(char *array, cryptogram cg)
  requires [_]public_invar(?pub) &*&
           [?f]crypto_chars(_, array, ?n, ?ccs) &*&
           ccs == ccs_for_cg(cg) &*&
           [_]public_generated(pub)(ccs);
  ensures  [f]chars(array, n, ?cs) &*& ccs == cs_to_ccs(cs) &*&
           true == cg_is_generated(cg) &*& [_]pub(cg);
{
  open [_]public_generated(pub)(ccs);
  dummy_foreach_extract(cg, cgs_in_ccs(ccs));
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
  ensures  [_]public_generated(pub)(ccs_for_cg(cg));
{
  cg_constraints(cg);
  dummy_foreach_singleton(pub, cg);
  close public_generated(pub)(ccs_for_cg(cg));
  leak public_generated(pub)(ccs_for_cg(cg));
}

lemma void public_generated_extract(predicate(cryptogram) pub,
                                    list<crypto_char> ccs, 
                                    cryptogram cg)
  requires [_]public_generated(pub)(ccs) &*&
           mem(cg,cgs_in_ccs(ccs)) || ccs == ccs_for_cg(cg);
  ensures  true == cg_is_generated(cg) &*& [_]pub(cg);
{
  open [_]public_generated(pub)(ccs);
  forall_mem(cg, cgs_in_ccs(ccs), cg_is_generated);
  dummy_foreach_extract(cg, cgs_in_ccs(ccs));
}

lemma void public_generated_split(predicate(cryptogram) pub,
                                  list<crypto_char> ccs, int i)
  requires 0 <= i && i <= length(ccs) &*&
           [_]public_generated(pub)(ccs);
  ensures  [_]public_generated(pub)(take(i, ccs)) &*&
           [_]public_generated(pub)(drop(i, ccs));
{
  open [_]public_generated(pub)(ccs);
  list<crypto_char> ccs1 = take(i, ccs);
  list<crypto_char> ccs2 = drop(i, ccs);
  list<cryptogram> cgs = cgs_in_ccs(ccs);
  list<cryptogram> cgs1 = cgs_in_ccs(ccs1);
  list<cryptogram> cgs2 = cgs_in_ccs(ccs2);
  cgs_in_ccs_upper_bound_split(ccs, cgs, i);
  cgs_in_ccs_upper_bound_superset(take(i, ccs), cgs1, cgs);
  cgs_in_ccs_upper_bound_superset(drop(i, ccs), cgs2, cgs);
  dummy_foreach_subset(cgs1, cgs);
  forall_subset(cgs1, cgs, cg_is_generated);
  dummy_foreach_subset(cgs2, cgs);
  forall_subset(cgs2, cgs, cg_is_generated);
  close public_generated(pub)(ccs1);
  leak  public_generated(pub)(ccs1);
  close public_generated(pub)(ccs2);
  leak  public_generated(pub)(ccs2);
}

lemma void public_generated_join(predicate(cryptogram) pub,
                                 list<crypto_char> ccs1, 
                                 list<crypto_char> ccs2)
  requires [_]public_generated(pub)(ccs1) &*&
           [_]public_generated(pub)(ccs2);
  ensures  [_]public_generated(pub)(append(ccs1, ccs2));
{
  open [_]public_generated(pub)(ccs1);
  open [_]public_generated(pub)(ccs2);
  list<crypto_char> ccs3 = append(ccs1, ccs2);
  list<cryptogram> cgs1 = cgs_in_ccs(ccs1);
  list<cryptogram> cgs2 = cgs_in_ccs(ccs2);
  list<cryptogram> cgs3 = cgs_in_ccs(ccs3);
  cgs_in_ccs_upper_bound_(ccs1);
  cgs_in_ccs_upper_bound_(ccs2);
  cgs_in_ccs_upper_bound_join(ccs1, cgs1, ccs2, cgs2);
  assert true == subset(cgs3, union(cgs1, cgs2));
  dummy_foreach_union(cgs1, cgs2);
  dummy_foreach_subset(cgs_in_ccs(ccs3), union(cgs1, cgs2));
  forall_union(cgs1, cgs2, cg_is_generated);
  forall_subset(cgs3, union(cgs1, cgs2), 
                cg_is_generated);
  close public_generated(pub)(ccs3);
  leak public_generated(pub)(ccs3);
}

@*/