#include "well_formed.h"

/*@

lemma char well_formed_valid_tag(nat len, list<crypto_char> ccs)
  requires FORALLP_C &*& FORALLP_CS &*&
           true == well_formed_ccs(forallc, forallcs, len, ccs);
  ensures  valid_tag(result) && head(ccs) == c_to_cc(result) &*&
           take(TAG_LENGTH, ccs) == full_ctag(head(ccs)) &*&
           take(TAG_LENGTH, ccs) == cs_to_ccs(full_tag(result));
{
  switch(len) {case succ(n): case zero:}
  list<crypto_char> ccs_tag =  take(TAG_LENGTH, ccs);
  list<crypto_char> ccs_cont = drop(TAG_LENGTH, ccs);
  head_append(ccs_tag, ccs_cont);
  char result = not_forall_t(forallc, (notf)((valid_ctag)(head(ccs))));
  cs_to_ccs_full_tag(result);
  return result;
}

lemma void well_formed_upper_bound(nat upper_bound1, nat upper_bound2,
                                   list<crypto_char> ccs)
  requires FORALLP_C &*& FORALLP_CS &*&
           true == well_formed_ccs(forallc, forallcs, upper_bound1, ccs) &*&
           length(ccs) <= int_of_nat(upper_bound2);
  ensures  true == well_formed_ccs(forallc, forallcs, upper_bound2, ccs);
{
  switch(upper_bound1)
  {
    case zero: assert false;
    case succ(n_ub1):
      switch(upper_bound2)
      {
        case zero: assert false;
        case succ(n_ub2):
          if (head(ccs) == c_to_cc(TAG_PAIR))
          {
            assert length(ccs) > TAG_LENGTH + 1;
            list<crypto_char> ccs_cont = drop(TAG_LENGTH, ccs);
            fixpoint(list<crypto_char>, bool) wf1 =
              (well_formed_ccs)(forallc, forallcs, n_ub1);
            fixpoint(list<crypto_char>, bool) wf2 =
              (well_formed_ccs)(forallc, forallcs, n_ub2);
            char c = not_forall_t(forallc,
              (notf)((well_formed_pair)(forallcs, wf1, ccs_cont)));

            int length_f_ccs, length_s_ccs;
            list<crypto_char> p_ccs, f_ccs, s_ccs;

            if (INT_MIN <= c && INT_MAX >= c)
            {
              list<char> cs_flength = not_forall_t(forallcs,
                (notf)((well_formed_pair_bounded)(wf1, ccs_cont)));
              length_f_ccs = int_of_chars(cs_flength);
              length_s_ccs = length(ccs_cont) - sizeof(int) - length_f_ccs;
              assert length(ccs_cont) > sizeof(int) + length_f_ccs;
              p_ccs = drop(sizeof(int), ccs_cont);
              length_drop(sizeof(int), ccs_cont);
              drop_drop(sizeof(int), TAG_LENGTH, ccs);
              f_ccs = take(length_f_ccs, p_ccs);
              s_ccs = drop(length_f_ccs, p_ccs);
              assert length(ccs_cont) > sizeof(int) + length_f_ccs;
              append_drop_take(p_ccs, length_f_ccs);
              assert p_ccs == append(f_ccs, s_ccs);
              append_drop_take(ccs_cont, sizeof(int));

              well_formed_upper_bound(n_ub1, n_ub2, f_ccs);
              well_formed_upper_bound(n_ub1, n_ub2, s_ccs);
              if (!exists_t<list<char> >(forallcs,
                    (well_formed_pair_bounded)(wf2, ccs_cont)))
              {
                forall_t_elim(forallcs,
                  (notf)((well_formed_pair_bounded)(wf2, ccs_cont)), cs_flength);
                assert false;
              }
            }
            else
            {
              length_f_ccs = c;
              length_s_ccs = length(ccs_cont) - 1 - length_f_ccs;
              p_ccs = drop(1, ccs_cont);
              f_ccs = take(length_f_ccs, p_ccs);
              s_ccs = drop(length_f_ccs, p_ccs);
              append_drop_take(p_ccs, length_f_ccs);
              assert p_ccs == append(f_ccs, s_ccs);
              take_1(ccs_cont);
              append_drop_take(ccs_cont, 1);
              assert ccs_cont == cons(c_to_cc(c), p_ccs);
              drop_drop(1, TAG_LENGTH, ccs);
              assert p_ccs == drop(TAG_LENGTH + 1, ccs);
              well_formed_upper_bound(n_ub1, n_ub2, f_ccs);
              well_formed_upper_bound(n_ub1, n_ub2, s_ccs);
            }
            if (!exists_t(forallc, (well_formed_pair)(forallcs, wf2, ccs_cont)))
            {
              forall_t_elim(forallc,
                (notf)((well_formed_pair)(forallcs, wf2, ccs_cont)), c);
              assert false;
            }
            assert true == well_formed_ccs(forallc, forallcs, upper_bound2, ccs);
          }
      }
  }
}

@*/
