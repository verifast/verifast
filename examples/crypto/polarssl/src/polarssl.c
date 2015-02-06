#include "../annotated_api/polarssl.h"

/*@

lemma void polarssl_public_message_from_cryptogram(
                   predicate(polarssl_cryptogram) polarssl_pub,
                   char* chars, int len, list<char> cs, polarssl_cryptogram cg)
  requires polarssl_cryptogram(chars, len, cs, cg) &*&
           [_]polarssl_pub(cg);
  ensures  polarssl_public_message(polarssl_pub)(chars, len, cs);
{
  open polarssl_cryptogram(chars, len, cs, cg);
  polarssl_generated_public_cryptograms_to(polarssl_pub, cg);
  assert true == mem(cg, polarssl_generated_public_cryptograms(polarssl_pub));
  assert true == polarssl_cryptograms_in_chars_upper_bound(cs, cons(cg, nil));
  assert true == subset(cons(cg, nil), 
                        polarssl_generated_public_cryptograms(polarssl_pub));
  polarssl_cryptograms_in_chars_upper_bound_subset(cs, cons(cg, nil), 
                        polarssl_generated_public_cryptograms(polarssl_pub));
  close polarssl_public_message(polarssl_pub)(chars, len, cs);
}

lemma void polarssl_public_message_from_chars(
                   predicate(polarssl_cryptogram) polarssl_pub,
                   char* chars, int len, list<char> cs)
  requires chars(chars, len, cs) &*&
           true == subset(polarssl_cryptograms_in_chars(cs),
                          polarssl_generated_public_cryptograms(polarssl_pub));
  ensures  polarssl_public_message(polarssl_pub)(chars, len, cs);
{
  polarssl_cryptograms_in_chars_upper_bound_to(
                                         cs, polarssl_cryptograms_in_chars(cs));
  polarssl_cryptograms_in_chars_upper_bound_subset(
                           cs, polarssl_cryptograms_in_chars(cs), 
                           polarssl_generated_public_cryptograms(polarssl_pub));
  close polarssl_public_message(polarssl_pub)(chars, len, cs);
}

lemma void polarssl_cryptogram_in_upper_bound(
                                          list<char> cs, polarssl_cryptogram cg,
                                          list<polarssl_cryptogram> cgs)
  requires cs == polarssl_chars_for_cryptogram(cg) &&
           true == polarssl_cryptograms_in_chars_upper_bound(cs, cgs);
  ensures  true == mem(cg, cgs);
{
  polarssl_cryptograms_in_chars_upper_bound_from(cs, cgs);
  assert true == subset(polarssl_cryptograms_in_chars(cs), cgs);
  polarssl_cryptogram_constraints(cs, cg);
  assert cons(cg, nil) == polarssl_cryptograms_in_chars(cs);
}

lemma void polarssl_cryptograms_in_chars_public_upper_bound_join(
                                   predicate(polarssl_cryptogram) polarssl_pub,
                                   list<char> cs1, list<char> cs2)
  requires polarssl_cryptograms_in_chars_upper_bound(cs1, 
                        polarssl_generated_public_cryptograms(polarssl_pub)) &&
           polarssl_cryptograms_in_chars_upper_bound(cs2, 
                        polarssl_generated_public_cryptograms(polarssl_pub));
  ensures  true == polarssl_cryptograms_in_chars_upper_bound(append(cs1, cs2),
                        polarssl_generated_public_cryptograms(polarssl_pub));
{
  polarssl_cryptograms_in_chars_upper_bound_join(
    cs1, polarssl_generated_public_cryptograms(polarssl_pub),
    cs2, polarssl_generated_public_cryptograms(polarssl_pub));
  union_refl(polarssl_generated_public_cryptograms(polarssl_pub));
}

lemma void polarssl_cryptograms_in_chars_public_upper_bound_split(
                                   predicate(polarssl_cryptogram) polarssl_pub,
                                   list<char> cs, int i)
     requires 0 <= i && i <= length(cs) &&
              polarssl_cryptograms_in_chars_upper_bound(cs,
                         polarssl_generated_public_cryptograms(polarssl_pub));
     ensures  polarssl_cryptograms_in_chars_upper_bound(take(i, cs), 
                         polarssl_generated_public_cryptograms(polarssl_pub)) &&
              polarssl_cryptograms_in_chars_upper_bound(drop(i, cs), 
                         polarssl_generated_public_cryptograms(polarssl_pub));
{
  polarssl_cryptograms_in_chars_upper_bound_split(cs,
                        polarssl_generated_public_cryptograms(polarssl_pub), i);
}

lemma void polarssl_generated_public_cryptograms_upper_bound(
                                    predicate(polarssl_cryptogram) polarssl_pub,
                                    polarssl_cryptogram cg)
  requires true == polarssl_cryptogram_is_generated(cg) &*& [_]polarssl_pub(cg);
  ensures  true == polarssl_cryptograms_in_chars_upper_bound(
                           polarssl_chars_for_cryptogram(cg),
                           polarssl_generated_public_cryptograms(polarssl_pub));
{
  polarssl_cryptogram_constraints(polarssl_chars_for_cryptogram(cg), cg);
  polarssl_cryptograms_in_chars_upper_bound_to(polarssl_chars_for_cryptogram(cg),
                                               cons(cg, nil));
  polarssl_generated_public_cryptograms_to(polarssl_pub, cg);
  assert true == subset(cons(cg, nil),
                        polarssl_generated_public_cryptograms(polarssl_pub));
  polarssl_cryptograms_in_chars_upper_bound_subset(
                           polarssl_chars_for_cryptogram(cg), cons(cg, nil),
                           polarssl_generated_public_cryptograms(polarssl_pub));
}

lemma void polarssl_cryptograms_generated_level_upper_bound(
                                                  list<polarssl_cryptogram> cgs)
  requires true == forall(cgs, polarssl_cryptogram_is_generated);
  ensures  true == forall(cgs, (polarssl_cryprogram_has_lower_level)
                               (succ(polarssl_cryprogram_level_upper_bound())));
{
  switch(cgs)
  {
    case cons(cg0, cgs0):
      polarssl_cryprogram_level_upper_bound_apply(cg0);
      polarssl_cryptograms_generated_level_upper_bound(cgs0);
    case nil:
      assert true;
  }
}

lemma void polarssl_cryptograms_in_chars_generated(
                                    predicate(polarssl_cryptogram) polarssl_pub,
                                    list<char> cs)
  requires true == subset(polarssl_cryptograms_in_chars(cs),
                          polarssl_generated_public_cryptograms(polarssl_pub));
  ensures  true == forall(polarssl_cryptograms_in_chars(cs), 
                          polarssl_cryptogram_is_generated);
{
  {
    lemma void polarssl_cryptograms_in_chars_generated_core( 
                                                  list<polarssl_cryptogram> cgs)
      requires true == subset(cgs,
                           polarssl_generated_public_cryptograms(polarssl_pub));
      ensures  true == forall(cgs, polarssl_cryptogram_is_generated);
    {
      switch(cgs)
      {
        case cons(cg0, cgs0):
          polarssl_generated_public_cryptograms_from(polarssl_pub, cg0);
          polarssl_cryptograms_in_chars_generated_core(cgs0);
        case nil:
          assert true;
      }
    }
    polarssl_cryptograms_in_chars_generated_core(
                                             polarssl_cryptograms_in_chars(cs));
  }
}

lemma void polarssl_generated_public_cryptograms_subset(
                                    predicate(polarssl_cryptogram) polarssl_pub,
                                    list<char> cs)
  requires true == subset(polarssl_cryptograms_in_chars(cs),
                          polarssl_generated_public_cryptograms(polarssl_pub));
  ensures  true == polarssl_cryptograms_in_chars_upper_bound(
                       cs, polarssl_generated_public_cryptograms(polarssl_pub));
{
  polarssl_cryptograms_in_chars_upper_bound_to(
                                         cs, polarssl_cryptograms_in_chars(cs));
  polarssl_cryptograms_in_chars_upper_bound_subset(cs,
                polarssl_cryptograms_in_chars(cs), 
                polarssl_generated_public_cryptograms(polarssl_pub));
}

lemma void polarssl_cryptograms_in_chars_split(list<char> cs, int i)
  requires 0 <= i && i <= length(cs);
  ensures  subset(polarssl_cryptograms_in_chars(take(i, cs)), 
                  polarssl_cryptograms_in_chars(cs)) &&
           subset(polarssl_cryptograms_in_chars(drop(i, cs)), 
                  polarssl_cryptograms_in_chars(cs));
{
  polarssl_cryptograms_in_chars_upper_bound_to(
                                         cs, polarssl_cryptograms_in_chars(cs));
  polarssl_cryptograms_in_chars_upper_bound_split(
                                      cs, polarssl_cryptograms_in_chars(cs), i);
  polarssl_cryptograms_in_chars_upper_bound_from(
                                take(i, cs), polarssl_cryptograms_in_chars(cs));
  polarssl_cryptograms_in_chars_upper_bound_from(
                                drop(i, cs), polarssl_cryptograms_in_chars(cs));
}

lemma void polarssl_cryptogram_level_nested_constraints_upper_bound(
                                       polarssl_cryptogram cg, nat upper_bound)
  requires polarssl_cryptogram_is_nested(cg) &&
           polarssl_cryptogram_is_generated(cg) &&
           polarssl_cryprogram_has_lower_level(succ(upper_bound), cg);
  ensures  true == forall(
                 polarssl_cryptograms_in_chars(polarssl_cryptogram_payload(cg)),
                            (polarssl_cryprogram_has_lower_level)(upper_bound));
{
  list<polarssl_cryptogram> cgs = 
                 polarssl_cryptograms_in_chars(polarssl_cryptogram_payload(cg));
  int l = length(cgs);
  
  while (0 < l)
    invariant 0 <= l &*& l <= length(cgs) &*&
              polarssl_cryptogram_is_generated(cg) &&
              true == forall(drop(l, cgs), (polarssl_cryprogram_has_lower_level)
                                           (upper_bound));
    decreases l;
  {
    list<polarssl_cryptogram> cgs1 = drop(l, cgs);
    assert true == forall(drop(l, cgs), (polarssl_cryprogram_has_lower_level)
                                        (upper_bound));
    l = l - 1;
    drop_n_plus_one(l, cgs);
    list<polarssl_cryptogram> cgs2 = drop(l, cgs);
    polarssl_cryptogram cg0 = head(cgs2);
    assert cgs2 == cons(cg0, cgs1);
    polarssl_cryptogram_level_nested_constraints(cg, cg0);
  }
}

@*/

