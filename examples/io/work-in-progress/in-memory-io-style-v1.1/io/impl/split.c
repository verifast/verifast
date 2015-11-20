//@ #include "split_body.gh"
//@ #include "token_body.gh"
//@ #include "../../../in-memory-io-style/helpers/cooked_ghost_lists.gh"
//@ #include <listex.gh>

/*@
fixpoint list<pair<int, place> > kplaces_new(
  list<pair<int, place> > kplaces, int n, int k, place t1, place t2, place t3
){
  return
    append(append(remove(pair(k,t1),kplaces), {pair(n,t2)}), {pair(n+1,t3)});
}

lemma void allpairs_g_implies_r(
  list<pair<int, place> > kplaces,
  int n,
  int k,
  place t1,
  place t2,
  place t3
)
requires allpairs_g_implies_r(kplaces);
ensures allpairs_g_implies_r(kplaces_new(kplaces, n, k, t1, t2, t3));
{
  assume(false); // XXX
}


lemma void lemma_r_is_transitive(
  int k, place t1,
  int k_new, place t_new,
  int k_other, place t_other,
  list<int> sigma
)
requires
  [_]kplace_r_is_transitive(pair(k,t1))
  &*& [_]split_helper(t1, t_new, t_other);
ensures
  [_]kplace_r_is_transitive(pair(k_new, t_new));
{
  open split_helper(t1, t_new, t_other);
  open kplace_r_is_transitive(pair(k,t1));
  close kplace_r_is_transitive(pair(k_new, t_new));
  leak kplace_r_is_transitive(pair(k_new, t_new));
}



lemma void lemma_i_holds(
  int k, place t1,
  int k_new, place t_new,
  int k_other, place t_other,
  list<int> sigma
)
requires
  [_]kplace_r_is_reflexive(pair(k_new,t_new))
  &*& true==kplace_i_holds(sigma, pair(k,t1))
  &*& [_]is_forall_t<list<int> >(?forall)
  &*& [_]split_helper(t1, t_new, t_other);
ensures
  true==kplace_i_holds(sigma, pair(k_new, t_new));
{
  open split_helper(t1, t_new, t_other);
  set_subset_property(place_i(t1), place_i(t_new), sigma);
}

lemma void lemma_r_preserves_i(
  int k, place t1,
  int k_new, place t_new,
  int k_other, place t_other
)
requires
  [_]split_helper(t1, t_new, t_other);
ensures [_]set_relation_preserves_set(place_r(t_new), place_i(t_new));
{
  open split_helper(_, _, _);
}


lemma void lemma_r_is_reflexive(
  int k, place t1,
  int k_new, place t_new,
  int k_other, place t_other
)
requires
  [_]kplace_r_is_reflexive(pair(k,t1));
ensures
  [_]kplace_r_is_reflexive(pair(k_new, t_new));
{
  assume(false); // XXX
}


lemma void split()
nonghost_callers_only
requires
  split(?t1, ?t2, ?t3)
  &*& token(?inst, t1)
  &*& all_tokens_invar(inst, ?sigma);
ensures token(inst, t2) &*& token(inst, t3) &*& all_tokens_invar(inst, sigma);
{
  open split(t1, t2, t3);
  open split_helper(t1, t2, t3); // openclose to get t1.inst=t2.inst
  close split_helper(t1, t2, t3);
  leak split_helper(t1, t2, t3);
  leak split_helper(t1, t3, t2);
  open token(inst, t1);
  open all_tokens_invar(_, _);
  
  assert cooked_ghost_list_member_handle(?id_list, ?k, t1);
  cooked_ghost_list_match(id_list, k);
  assert cooked_ghost_list(id_list, ?n, ?kplaces);
  
  assert true==mem(pair(k,t1), kplaces);
  
  cooked_ghost_list_remove(id_list, k);
  
  cooked_ghost_list_add(id_list, t2);
  assert cooked_ghost_list_member_handle(id_list, _, t2);
  close token(inst, t2);
  cooked_ghost_list_add(id_list, t3);
  close token(inst, t3);
  
  assert [_]is_forall_t<list<int> >(?forall_sigma);
  assert [_]is_forall_t<pair<list<int>, list<int> > >(?forall_sigmapairs);
  
  foreach_remove(pair(k, t1), kplaces);
  
  open kplace_all_properties(sigma)(pair(k, t1));
  
  lemma_r_is_reflexive(k, t1, n, t2, n+1, t3);
  lemma_r_is_reflexive(k, t1, n+1, t3, n, t2);
  
  lemma_i_holds(k, t1, n, t2, n+1, t3, sigma);
  lemma_i_holds(k, t1, n+1, t3, n, t2, sigma);
  
  lemma_r_is_transitive(k, t1, n, t2, n+1, t3, sigma);
  lemma_r_is_transitive(k, t1, n+1, t3, n, t2, sigma);
  
  lemma_r_preserves_i(k, t1, n, t2, n+1, t3);
  lemma_r_preserves_i(k, t1, n+1, t3, n, t2);

  allpairs_g_implies_r(kplaces, n, k, t1, t2, t3);
  
  close foreach({}, kplace_all_properties(sigma));
  close kplace_all_properties(sigma)(pair(n, t2));
  close foreach({pair(n, t2)}, kplace_all_properties(sigma));
  foreach_append(remove( pair(k,t1), kplaces),{pair(n,t2)});
  // and again:
  close foreach({}, kplace_all_properties(sigma));
  close kplace_all_properties(sigma)(pair(n+1, t3));
  close foreach({pair(n+1, t3)}, kplace_all_properties(sigma));
  foreach_append(append(remove(pair(k,t1),kplaces), {pair(n,t2)}),{pair(n+1,t3)});
  
  close all_tokens_invar(inst, sigma);
  open split_helper(_, _, _);
  open split_helper(_, _, _);
}

@*/
