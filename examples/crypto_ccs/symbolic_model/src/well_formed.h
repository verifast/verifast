#ifndef WELL_FORMED_H
#define WELL_FORMED_H

#include "item_tags.h"
//@ #include "quantifiers.gh"

/*@

#define FORALL_C   fixpoint(fixpoint(char, bool), bool) forallc
#define FORALL_CS  fixpoint(fixpoint(list<char>, bool), bool) forallcs
#define FORALLP_C  [_]is_forall_t<char>(?forallc)
#define FORALLP_CS [_]is_forall_t<list<char> >(?forallcs)

fixpoint bool valid_ctag(crypto_char cc, char c)
{
  return c_to_cc(c) == cc && valid_tag(c);
}
fixpoint bool valid_full_ctag(FORALL_C, list<crypto_char> ccs)
{
  return length(ccs) == TAG_LENGTH &&
         take(TAG_LENGTH, ccs) == full_ctag(head(ccs)) &&
         exists_t<char>(forallc, (valid_ctag)(head(ccs)));
}

fixpoint bool well_formed_pair_bounded(fixpoint(list<crypto_char>, bool) wf,
                                       list<crypto_char> ccs_cont,
                                       list<char> cs_flength)
{
  return cs_to_ccs(cs_flength) == take(sizeof(int), ccs_cont) &&
         int_of_chars(cs_flength) > 0 &&
         length(ccs_cont) > sizeof(int) +
                            int_of_chars(cs_flength) &&
         wf(take(int_of_chars(cs_flength), drop(sizeof(int), ccs_cont))) &&
         wf(drop(int_of_chars(cs_flength), drop(sizeof(int), ccs_cont)));
}

fixpoint bool well_formed_pair(FORALL_CS,
                               fixpoint(list<crypto_char>, bool) wf,
                               list<crypto_char> ccs_cont, char c)
{
  return c_to_cc(c) == head(ccs_cont) &&
         (
           INT_MIN <= c && INT_MAX >= c ?
             exists_t<list<char> >(forallcs,
               (well_formed_pair_bounded)(wf, ccs_cont))
           :
             c > 0 && length(ccs_cont) > 1 + c &&
             wf(take(c, drop(1, ccs_cont))) &&
             wf(drop(c, drop(1, ccs_cont)))
         );
}

fixpoint bool well_formed_ccs(FORALL_C, FORALL_CS, nat n, list<crypto_char> ccs)
{
  switch(n)
  {
    case succ(n0):
      return
        //correct total length
        length(ccs) > TAG_LENGTH &&
        //correct tag
        valid_full_ctag(forallc, take(TAG_LENGTH, ccs)) &&
        //correct data_item
        (
          head(ccs) != c_to_cc(TAG_DATA) ||
          true
        ) &&
        //correct pair_item
        (
          head(ccs) != c_to_cc(TAG_PAIR) ||
          (
            length(ccs) > TAG_LENGTH + 1 &&
            exists_t<char>(forallc,
              (well_formed_pair)(forallcs,
                                 (well_formed_ccs)(forallc, forallcs, n0),
                                 drop(TAG_LENGTH, ccs)))
          )
        ) &&
        //correct nonce_item
        (
          head(ccs) != c_to_cc(TAG_NONCE) ||
          length(ccs) == TAG_LENGTH + 1 + NONCE_SIZE
        ) &&
        //correct hash_item
        (
          head(ccs) != c_to_cc(TAG_HASH) ||
          length(ccs) == TAG_LENGTH + HASH_SIZE
        ) &&
        //correct symmetric_key_item
        (
          head(ccs) != c_to_cc(TAG_SYMMETRIC_KEY) ||
          length(ccs) == TAG_LENGTH + GCM_KEY_SIZE
        ) &&
        //correct public_key_item
        (
          head(ccs) != c_to_cc(TAG_PUBLIC_KEY) ||
          length(ccs) == TAG_LENGTH + RSA_SERIALIZED_KEY_SIZE
        ) &&
        //correct private_key_item
        (
          head(ccs) != c_to_cc(TAG_PRIVATE_KEY) ||
          length(ccs) == TAG_LENGTH + RSA_SERIALIZED_KEY_SIZE
        ) &&
        //correct hmac_item
        (
          head(ccs) != c_to_cc(TAG_HMAC) ||
          length(ccs) == TAG_LENGTH + HMAC_SIZE
        ) &&
        //correct symmetric_encrypted_item
        (
          head(ccs) != c_to_cc(TAG_SYMMETRIC_ENC) ||
          length(ccs) >= TAG_LENGTH + MINIMAL_STRING_SIZE + GCM_IV_SIZE
        ) &&
        //correct asymmetric_encrypted_item
        (
          head(ccs) != c_to_cc(TAG_ASYMMETRIC_ENC) ||
          (length(ccs) <= TAG_LENGTH + RSA_SERIALIZED_KEY_SIZE &&
           length(ccs) >= TAG_LENGTH + MINIMAL_STRING_SIZE)
        ) &&
        //correct asymmetric_signed_item
        (
          head(ccs) != c_to_cc(TAG_ASYMMETRIC_SIG) ||
          (length(ccs) <= TAG_LENGTH + RSA_SERIALIZED_KEY_SIZE &&
           length(ccs) >= TAG_LENGTH + MINIMAL_STRING_SIZE)
        );
    case zero:
      return false;
  }
}

lemma char well_formed_valid_tag(nat len, list<crypto_char> ccs);
  requires FORALLP_C &*& FORALLP_CS &*&
           true == well_formed_ccs(forallc, forallcs, len, ccs);
  ensures  valid_tag(result) && head(ccs) == c_to_cc(result) &*&
           take(TAG_LENGTH, ccs) == full_ctag(head(ccs)) &*&
           take(TAG_LENGTH, ccs) == cs_to_ccs(full_tag(result));

lemma void well_formed_upper_bound(nat upper_bound1, nat upper_bound2,
                                   list<crypto_char> ccs);
  requires FORALLP_C &*& FORALLP_CS &*&
           true == well_formed_ccs(forallc, forallcs, upper_bound1, ccs) &*&
           length(ccs) <= int_of_nat(upper_bound2);
  ensures  true == well_formed_ccs(forallc, forallcs, upper_bound2, ccs);

predicate_ctor well_formed_item_ccs(item i)(list<crypto_char> ccs) =
  FORALLP_C &*& FORALLP_CS &*&
  true == well_formed_ccs(forallc, forallcs, nat_length(ccs), ccs)
;

predicate_ctor ill_formed_item_ccs(item i)(list<crypto_char> ccs) =
  FORALLP_C &*& FORALLP_CS &*&
  false == well_formed_ccs(forallc, forallcs, nat_length(ccs), ccs)
;

@*/

#endif
