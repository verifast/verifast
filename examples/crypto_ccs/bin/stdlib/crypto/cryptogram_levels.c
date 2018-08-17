//@ #include "cryptogram_levels.gh"

/*@

lemma void cg_level_ccs_max(list<crypto_char> ccs)
  requires true;
  ensures  [_]is_forall_t<cryptogram>(?forallcg) &*&
           true == forallcg((cg_in_ccs_implies_level_below)(ccs, cg_level_max));
{
  get_forall_t<cryptogram>();
  assert [_]is_forall_t<cryptogram>(?forallcg);
  fixpoint(cryptogram, bool) p = (cg_in_ccs_implies_level_below)(ccs, cg_level_max);
  if (!forallcg(p))
  {
    cryptogram cg = not_forall_t(forallcg, p);
    cg_level_max_(cg);
    assert false;
  }
}

lemma void cg_level_ccs_pay(cryptogram cg, nat bound)
  requires cg_payload(cg) == some(?pay) &*& cg_is_gen_or_pub(cg) &&
           cg_level_below(succ(bound), cg);
  ensures  [_]is_forall_t<cryptogram>(?forallcg) &*&
           true == forallcg((cg_in_ccs_implies_level_below)(pay, bound));
{
  get_forall_t<cryptogram>();
  assert [_]is_forall_t<cryptogram>(?forallcg);
  fixpoint(cryptogram, bool) p = (cg_in_ccs_implies_level_below)(pay, bound);
  if (!forallcg(p))
  {
    cryptogram cg_pay = not_forall_t(forallcg, p);
    cg_level_ind(cg, cg_pay);
    assert false;
  }
}

lemma void cg_level_ccs_sublist(list<crypto_char> ccs,
                                list<crypto_char> ccs_part, nat bound)
  requires [_]is_forall_t<cryptogram>(?forallcg) &*&
           true == sublist(ccs_part, ccs) &*&
           true == forallcg((cg_in_ccs_implies_level_below)(ccs, bound));
  ensures  true == forallcg((cg_in_ccs_implies_level_below)(ccs_part, bound));
{
  fixpoint(cryptogram, bool) p = (cg_in_ccs_implies_level_below)(ccs_part, bound);
  if (!forallcg(p))
  {
    cryptogram cg = not_forall_t(forallcg, p);
    forall_t_elim(forallcg, (cg_in_ccs_implies_level_below)(ccs, bound), cg);
    assert true == sublist(ccs_for_cg(cg), ccs_part);
    assert false == sublist(ccs_for_cg(cg), ccs);
    sublist_trans(ccs_for_cg(cg), ccs_part, ccs);
    assert false;
  }
}

@*/
