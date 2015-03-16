#include "../annotated_api/polarssl.h"
//@ #include "listex.gh"

/*@

lemma void polarssl_cryptogram_in_bound(list<char> cs, polarssl_cryptogram cg,
                                        list<polarssl_cryptogram> cgs)
  requires cs == polarssl_chars_for_cryptogram(cg) &&
           true == polarssl_cryptograms_in_chars_bound(cs, cgs);
  ensures  true == mem(cg, cgs);
{
  polarssl_cryptograms_in_chars_bound_from(cs, cgs);
  assert true == subset(polarssl_cryptograms_in_chars(cs), cgs);
  polarssl_cryptogram_constraints(cs, cg);
  assert cons(cg, nil) == polarssl_cryptograms_in_chars(cs);
}

lemma void polarssl_public_generated_cryptogram_chars(
                                    predicate(polarssl_cryptogram) polarssl_pub, 
                                    polarssl_cryptogram cg)
  requires true == polarssl_cryptogram_is_generated(cg) &*& [_]polarssl_pub(cg);
  ensures  [_]polarssl_public_generated_chars(polarssl_pub)(
                                             polarssl_chars_for_cryptogram(cg));
{
  list<polarssl_cryptogram> cgs = cons(cg, nil);
  list<char> cs = polarssl_chars_for_cryptogram(cg);
  close dummy_foreach(nil, polarssl_pub);
  leak dummy_foreach(nil, polarssl_pub);
  close dummy_foreach(cgs, polarssl_pub);
  leak dummy_foreach(cgs, polarssl_pub);
  polarssl_cryptogram_constraints(cs, cg);
  close polarssl_public_generated_chars(polarssl_pub)(cs);
  leak polarssl_public_generated_chars(polarssl_pub)(cs);
}

lemma void polarssl_public_generated_chars_extract(
                                    predicate(polarssl_cryptogram) polarssl_pub,
                                    list<char> cs, polarssl_cryptogram cg)
  requires [_]polarssl_public_generated_chars(polarssl_pub)(cs) &*&
           true == mem(cg, polarssl_cryptograms_in_chars(cs)) ||
           cs == polarssl_chars_for_cryptogram(cg);
  ensures  true == polarssl_cryptogram_is_generated(cg) &*& [_]polarssl_pub(cg);
{
  open [_]polarssl_public_generated_chars(polarssl_pub)(cs);
  if (!mem(cg, polarssl_cryptograms_in_chars(cs)))
  {
    polarssl_cryptograms_in_chars_bound_to(cs);
    polarssl_cryptogram_in_bound(cs, cg, polarssl_cryptograms_in_chars(cs));
    assert false;
  }
  forall_mem(cg, polarssl_cryptograms_in_chars(cs), 
             polarssl_cryptogram_is_generated);
  dummy_foreach_extract(cg, polarssl_cryptograms_in_chars(cs));
}

lemma void polarssl_public_generated_chars_join(
                                   predicate(polarssl_cryptogram) polarssl_pub,
                                   list<char> cs1, list<char> cs2)
  requires [_]polarssl_public_generated_chars(polarssl_pub)(cs1) &*&
           [_]polarssl_public_generated_chars(polarssl_pub)(cs2);
  ensures  [_]polarssl_public_generated_chars(polarssl_pub)(append(cs1, cs2));
{
  open [_]polarssl_public_generated_chars(polarssl_pub)(cs1);
  open [_]polarssl_public_generated_chars(polarssl_pub)(cs2);
  list<char> cs3 = append(cs1, cs2);
  list<polarssl_cryptogram> cgs1 = polarssl_cryptograms_in_chars(cs1);
  list<polarssl_cryptogram> cgs2 = polarssl_cryptograms_in_chars(cs2);
  list<polarssl_cryptogram> cgs3 = polarssl_cryptograms_in_chars(cs3);
  polarssl_cryptograms_in_chars_bound_to(cs1);
  polarssl_cryptograms_in_chars_bound_to(cs2);
  polarssl_cryptograms_in_chars_bound_join(cs1, cgs1, cs2, cgs2);
  polarssl_cryptograms_in_chars_bound_from(cs3, union(cgs1, cgs2));
  assert true == subset(cgs3, union(cgs1, cgs2));
  dummy_foreach_union(cgs1, cgs2);
  dummy_foreach_subset(polarssl_cryptograms_in_chars(cs3), union(cgs1, cgs2));
  forall_union(cgs1, cgs2, polarssl_cryptogram_is_generated);
  forall_subset(cgs3, union(cgs1, cgs2), 
                polarssl_cryptogram_is_generated);
  close polarssl_public_generated_chars(polarssl_pub)(cs3);
  leak polarssl_public_generated_chars(polarssl_pub)(cs3);
}

lemma void polarssl_public_generated_chars_split(
                                   predicate(polarssl_cryptogram) polarssl_pub,
                                   list<char> cs, int i)
     requires 0 <= i && i <= length(cs) &*&
              [_]polarssl_public_generated_chars(polarssl_pub)(cs);
     ensures  [_]polarssl_public_generated_chars(polarssl_pub)(take(i, cs)) &*&
              [_]polarssl_public_generated_chars(polarssl_pub)(drop(i, cs));
{
  open [_]polarssl_public_generated_chars(polarssl_pub)(cs);
  list<polarssl_cryptogram> cgs = polarssl_cryptograms_in_chars(cs);
  polarssl_cryptograms_in_chars_bound_to(cs);
  polarssl_cryptograms_in_chars_bound_split(cs, cgs, i);
  polarssl_cryptograms_in_chars_bound_from(take(i, cs), cgs);
  polarssl_cryptograms_in_chars_bound_from(drop(i, cs), cgs);
  dummy_foreach_subset(polarssl_cryptograms_in_chars(take(i, cs)), cgs);
  dummy_foreach_subset(polarssl_cryptograms_in_chars(drop(i, cs)), cgs);
  forall_subset(polarssl_cryptograms_in_chars(take(i, cs)), cgs,
                polarssl_cryptogram_is_generated);
  forall_subset(polarssl_cryptograms_in_chars(drop(i, cs)), cgs,
                polarssl_cryptogram_is_generated);
  close polarssl_public_generated_chars(polarssl_pub)(take(i, cs));
  leak polarssl_public_generated_chars(polarssl_pub)(take(i, cs));
  close polarssl_public_generated_chars(polarssl_pub)(drop(i, cs));
  leak polarssl_public_generated_chars(polarssl_pub)(drop(i, cs));
}

lemma void polarssl_public_message_from_cryptogram(
                   predicate(polarssl_cryptogram) polarssl_pub,
                   char* chars, int len, list<char> cs, polarssl_cryptogram cg)
  requires polarssl_cryptogram(chars, len, cs, cg) &*&
           [_]polarssl_pub(cg);
  ensures  polarssl_public_message(polarssl_pub)(chars, len, cs);
{
  open polarssl_cryptogram(chars, len, cs, cg);
  polarssl_public_generated_cryptogram_chars(polarssl_pub, cg);
  close polarssl_public_message(polarssl_pub)(chars, len, cs);
}


lemma void polarssl_cryptogram_level_nested_constraints_bound(
                                       polarssl_cryptogram cg, nat bound)
  requires polarssl_cryptogram_is_nested(cg) &&
           polarssl_cryptogram_is_generated(cg) &&
           polarssl_cryprogram_has_lower_level(succ(bound), cg);
  ensures  true == forall(
                 polarssl_cryptograms_in_chars(polarssl_cryptogram_payload(cg)),
                            (polarssl_cryprogram_has_lower_level)(bound));
{
  list<polarssl_cryptogram> cgs = 
                 polarssl_cryptograms_in_chars(polarssl_cryptogram_payload(cg));
  int l = length(cgs);
  
  while (0 < l)
    invariant 0 <= l &*& l <= length(cgs) &*&
              polarssl_cryptogram_is_generated(cg) &&
              true == forall(drop(l, cgs), (polarssl_cryprogram_has_lower_level)
                                           (bound));
    decreases l;
  {
    list<polarssl_cryptogram> cgs1 = drop(l, cgs);
    assert true == forall(drop(l, cgs), (polarssl_cryprogram_has_lower_level)
                                        (bound));
    l = l - 1;
    drop_n_plus_one(l, cgs);
    list<polarssl_cryptogram> cgs2 = drop(l, cgs);
    polarssl_cryptogram cg0 = head(cgs2);
    assert cgs2 == cons(cg0, cgs1);
    polarssl_cryptogram_level_nested_constraints(cg, cg0);
  }
}

lemma void polarssl_cryptograms_generated_level_bound(
                                                  list<polarssl_cryptogram> cgs)
  requires true == forall(cgs, polarssl_cryptogram_is_generated);
  ensures  true == forall(cgs, (polarssl_cryprogram_has_lower_level)
                               (succ(polarssl_cryprogram_level_bound())));
{
  switch(cgs)
  {
    case cons(cg0, cgs0):
      polarssl_cryprogram_level_bound_apply(cg0);
      polarssl_cryptograms_generated_level_bound(cgs0);
    case nil:
      assert true;
  }
}

@*/

