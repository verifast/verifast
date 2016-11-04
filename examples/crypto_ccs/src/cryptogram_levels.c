//@ #include "../annotated_api/general_definitions/public_chars.gh"
//@ #include "../annotated_api/general_definitions/cryptogram_bounds.gh"

/*@

lemma void cg_level_max_forall(list<cryptogram> cgs)
  requires true;
  ensures true == forall(cgs, (cg_level_below)(cg_level_max));
{
  switch(cgs)
  {
    case cons(cg0, cgs0):
      cg_level_max_(cg0);
      cg_level_max_forall(cgs0);
    case nil:
  }
}

lemma void cg_level_pay(cryptogram cg, nat bound)
  requires cg_payload(cg) == some(?pay) &*& cg_is_generated(cg) &&
           cg_level_below(succ(bound), cg);
  ensures  true == forall(cgs_in_ccs(pay), (cg_level_below)(bound));
{
  list<cryptogram> cgs = cgs_in_ccs(pay);
  int l = length(cgs);
  
  while (0 < l)
    invariant 0 <= l &*& l <= length(cgs) &*&
              cg_is_generated(cg) &&
              forall(drop(l, cgs), (cg_level_below)(bound));
    decreases l;
  {
    list<cryptogram> cgs1 = drop(l, cgs);
    assert true == forall(drop(l, cgs), (cg_level_below)(bound));
    l = l - 1;
    drop_n_plus_one(l, cgs);
    list<cryptogram> cgs2 = drop(l, cgs);
    cryptogram cg0 = head(cgs2);
    assert cgs2 == cons(cg0, cgs1);
    cg_level_ind(cg, cg0);
  }
}

@*/