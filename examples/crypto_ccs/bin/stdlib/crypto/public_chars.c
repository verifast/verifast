//@ #include "public_chars.gh"

/*@

lemma void public_cs(list<char> cs)
  requires true;
  ensures  [_]public_ccs(cs_to_ccs(cs));
{
  get_forall_t<list<char> >();
  assert [_]is_forall_t<list<char> >(?forallcs);
  if (!exists_t<list<char> >(forallcs, (cs_to_ccs_eq)(cs_to_ccs(cs))))
  {
    forall_t_elim(forallcs, (notf)((cs_to_ccs_eq)(cs_to_ccs(cs))), cs);
  }
  close exists(cs);
  leak exists(cs);
  close public_ccs(cs_to_ccs(cs));
  leak public_ccs(cs_to_ccs(cs));
}

lemma_auto void public_chars(char *array, int size)
  requires [?f]chars(array, size, ?cs);
  ensures  [f]chars(array, size, cs) &*& [_]public_ccs(cs_to_ccs(cs));
{
  public_cs(cs);
}

lemma void public_ccs(char *array, int size)
  requires [?f]crypto_chars(?kind, array, size, ?ccs);
  ensures  switch(kind)
           {
             case normal:
               return [_]public_ccs(ccs);
             case secret:
                return col ? [_]public_ccs(ccs) : true;
           } &*& [f]crypto_chars(kind, array, size, ccs);
{
  if (kind == normal || col)
  {
    crypto_chars_to_chars(array, size);
    assert [f]chars(array, size, ?cs);
    public_cs(cs);
    if (kind == normal)
      chars_to_crypto_chars(array, size);
    else
      chars_to_secret_crypto_chars(array, size);
  }
}

lemma void public_cryptogram(char *array, cryptogram cg)
  requires [_]public_invar(?pub) &*&
           [?f]cryptogram(array, ?n, ?ccs, cg) &*& [_]pub(cg);
  ensures  [f]chars(array, n, ?cs) &*&
           [_]public_ccs(ccs) &*& ccs == cs_to_ccs(cs);
{
  open [f]cryptogram(array, n, ccs, cg);
  public_cg_ccs(cg);
  public_crypto_chars(array, n);
}

lemma void public_ccs_split(list<crypto_char> ccs, int i)
  requires 0 <= i && i <= length(ccs) &*&
           [_]public_ccs(ccs);
  ensures  [_]public_ccs(take(i, ccs)) &*&
           [_]public_ccs(drop(i, ccs));
{
  public_cs_to_ccs(ccs);
  assert [_]is_forall_t<list<char> >(?forallcs);
  list<char> cs = not_forall_t(forallcs, (notf)((cs_to_ccs_eq)(ccs)));
  list<char> cs1 = take(i, cs);
  list<char> cs2 = drop(i, cs);
  cs_to_ccs_take(i, cs);
  cs_to_ccs_drop(i, cs);
  public_cs(cs1);
  public_cs(cs2);
}

lemma void public_ccs_join(list<crypto_char> ccs1, list<crypto_char> ccs2)
  requires [_]public_ccs(ccs1) &*&
           [_]public_ccs(ccs2);
  ensures  [_]public_ccs(append(ccs1, ccs2));
{
  public_cs_to_ccs(ccs1);
  public_cs_to_ccs(ccs2);
  get_forall_t<list<char> >();
  assert [_]is_forall_t<list<char> >(?forallcs);
  list<char> cs1 = not_forall_t(forallcs, (notf)((cs_to_ccs_eq)(ccs1)));
  list<char> cs2 = not_forall_t(forallcs, (notf)((cs_to_ccs_eq)(ccs2)));
  list<char> cs = append(cs1, cs2);
  cs_to_ccs_append(cs1, cs2);
  public_cs(cs);
}

lemma void cs_to_ccs_crypto_chars(char *array, list<char> cs)
  requires [?f]crypto_chars(?kind, array, ?n, cs_to_ccs(cs));
  ensures  [f]chars(array, n, cs);
{
  public_cs(cs);
  public_crypto_chars(array, n);
  assert [f]chars(array, n, ?cs0);
  cs_to_ccs_inj(cs, cs0);
}

@*/