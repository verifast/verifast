#ifndef ITEM_CONSTRAINTS_H
#define ITEM_CONSTRAINTS_H

#include "well_formed.h"
// #include "item.h"
#include "invariants.h"

/*@

predicate_ctor ic_parts(item i)(list<crypto_char> ccs_tag,
                                list<crypto_char> ccs_cont) = true;
predicate_ctor ic_pair(item i)(list<crypto_char> ccs_f,
                               list<crypto_char> ccs_s) = true;
predicate_ctor ic_sym_enc(item i)(list<crypto_char> iv,
                                  list<crypto_char> cg_ccs) = true;
predicate_ctor ic_cg(item i)(list<crypto_char> ccs, cryptogram cg) = true;
predicate_ctor ic_info(item i)(list<crypto_char> ccs, char tag,
                               list<crypto_char> ccs_cont,
                               list<crypto_char> ccs_tag) = true;

#define IC_PUBLIC \
  [_]public_ccs(ccs_cont) &*& \
  [_]public_ccs(ccs)

#define IC_PUBLIC_IF_COLLISION \
  (col ? IC_PUBLIC : true)

#define IC_CG(CCS, CG) \
  length(CCS) >= MINIMAL_STRING_SIZE &*& \
  ic_cg(i)(CCS, ?cg) &*& cg == CG &*& \
  col || (CCS == ccs_for_cg(cg) && cg_is_gen_or_pub(cg))

#define IC_PAY(PAY, NONE) \
  col ? true : \
  switch(pay0) \
  { \
    case some(pay1): \
      return [_]well_formed_item_ccs(i)(PAY) &*& \
            length(PAY) <= INT_MAX &*& \
            [_]item_constraints(pay1, PAY, pub); \
    case none: \
      return [_]ill_formed_item_ccs(i)(PAY) &*& \
            length(PAY) <= INT_MAX &*& [_]public_ccs(PAY) &*& \
            NONE; \
  } \

predicate item_constraints(item i, list<crypto_char> ccs, predicate(item) pub) =
  FORALLP_C &*& FORALLP_CS &*&
  well_formed_ccs(forallc, forallcs, nat_length(ccs), ccs) &&
  length(ccs) <= INT_MAX &*& ic_parts(i)(?ccs_tag, ?ccs_cont) &*&
  ccs == append(ccs_tag, ccs_cont) &*&
  length(ccs_tag) == TAG_LENGTH &*& ccs_tag == full_ctag(head(ccs_tag)) &*&
  head(ccs_tag) == c_to_cc(tag_for_item(i)) &*&
  [_]public_ccs(ccs_tag) &*&
  IC_PUBLIC_IF_COLLISION &*&
  switch(i)
  {
    case data_item(cs1): return
        ccs_cont == cs_to_ccs(cs1) &*& IC_PUBLIC;
    case pair_item(f0, s0): return
        ic_pair(i)(?ccs_f0, ?ccs_s0) &*&
        [_]item_constraints(f0, ccs_f0, pub) &*&
        [_]item_constraints(s0, ccs_s0, pub) &*&
        length(ccs_cont) > sizeof(int) + length(ccs_f0) &*&
        take(sizeof(int), ccs_cont) ==
          cs_to_ccs(chars_of_unbounded_int(length(ccs_f0))) &*&
        drop(sizeof(int), ccs_cont) == append(ccs_f0, ccs_s0) &*&
        [_]public_ccs(take(sizeof(int), ccs_cont));
    case nonce_item(p0, c0, inc0): return
        ccs_cont == cons(c_to_cc(inc0), ?cs_cg) &*&
        [_]public_ccs(cons(c_to_cc(inc0), nil)) &*&
        length(cs_cg) == NONCE_SIZE &*&
        IC_CG(cs_cg, cg_nonce(p0, c0));
    case hash_item(pay0): return
        length(ccs_cont) == HASH_SIZE &*&
        IC_CG(ccs_cont, cg_sha512_hash(?ccs_pay1)) &*&
        IC_PAY(ccs_pay1, true);
    case symmetric_key_item(p0, c0): return
        length(ccs_cont) == GCM_KEY_SIZE &*&
        IC_CG(ccs_cont, cg_symmetric_key(p0, c0));
    case public_key_item(p0, c0): return
        length(ccs_cont) == RSA_SERIALIZED_KEY_SIZE &*&
        IC_CG(ccs_cont, cg_rsa_public_key(p0, c0));
    case private_key_item(p0, c0): return
        length(ccs_cont) == RSA_SERIALIZED_KEY_SIZE &*&
        IC_CG(ccs_cont, cg_rsa_private_key(p0, c0));
    case hmac_item(p0, c0, pay0): return
        IC_CG(ccs_cont, cg_sha512_hmac(p0, c0, ?ccs_pay1)) &*&
        IC_PAY(ccs_pay1, [_]pub(symmetric_key_item(p0, c0)));
    case symmetric_encrypted_item(p0, c0, pay0, ent0): return
        ic_sym_enc(i)(?iv0, ?cg_ccs) &*&
        take(GCM_IV_SIZE, ent0) == take(GCM_IV_SIZE, ccs_cont) &*&
        [_]public_ccs(take(GCM_IV_SIZE, ent0)) &*&
        length(ccs_cont) >= GCM_IV_SIZE &*& GCM_IV_SIZE <= length(ent0) &*&
        drop(GCM_IV_SIZE, ent0) == iv0 &*&
        cg_ccs == drop(GCM_IV_SIZE, ccs_cont) &*&
        IC_CG(cg_ccs, cg_aes_auth_encrypted(p0, c0, ?ccs_pay1, iv0)) &*&
        IC_PAY(ccs_pay1, [_]pub(symmetric_key_item(p0, c0)));
    case asymmetric_encrypted_item(p0, c0, pay0, ent0): return
        IC_CG(ccs_cont, cg_rsa_encrypted(p0, c0, ?ccs_pay1, ent0)) &*&
        IC_PAY(ccs_pay1, [_]pub(public_key_item(p0, c0)));
    case asymmetric_signature_item(p0, c0, pay0, ent0): return
        IC_CG(ccs_cont, cg_rsa_signature(p0, c0, ?ccs_pay1, ent0)) &*&
        IC_PAY(ccs_pay1, [_]pub(private_key_item(p0, c0)));
  }
;

#define OPEN_ITEM_CONSTRAINTS(I, CCS, PUB) \
  if (true) \
  { \
    open [_]item_constraints(I, CCS, PUB); \
    assert [_]ic_parts(I)(?ccs_tag00, ?ccs_cont00); \
    take_append(TAG_LENGTH, ccs_tag00, ccs_cont00); \
    drop_append(TAG_LENGTH, ccs_tag00, ccs_cont00); \
    assert CCS == append(ccs_tag00, ccs_cont00); \
    head_append(ccs_tag00, ccs_cont00); \
    cs_to_ccs_full_tag_for_item(I); \
    char tag00 = well_formed_valid_tag(nat_length(CCS), CCS); \
    c_to_cc_inj(tag00, tag_for_item(I)); \
    assert ccs_tag00 == take(TAG_LENGTH, CCS); \
    assert ccs_cont00 == drop(TAG_LENGTH, CCS); \
    close ic_info(I)(CCS, tag00, ccs_tag00, ccs_cont00); \
    leak ic_info(I)(CCS, tag00, ccs_tag00, ccs_cont00); \
  }

#define CLOSE_ITEM_CONSTRAINTS(P, TAG, SIZE, I) \
  if (true) \
  { \
    assert [?f01]chars(P, TAG_LENGTH, full_tag(TAG)); \
    chars_to_secret_crypto_chars(P, TAG_LENGTH); \
    public_cs(full_tag(TAG)); \
    assert [f01]crypto_chars(secret, P + TAG_LENGTH, SIZE - TAG_LENGTH, ?ccs_cont00); \
    cs_to_ccs_full_tag(TAG); \
    crypto_chars_join(P); \
    assert [f01]crypto_chars(secret, P, SIZE, ?ccs00); \
    assert ccs00 == append(full_ctag(c_to_cc(TAG)), ccs_cont00); \
    close ic_parts(I)(full_ctag(c_to_cc(TAG)), ccs_cont00); \
    take_append(TAG_LENGTH, full_ctag(c_to_cc(TAG)), ccs_cont00); \
    drop_append(TAG_LENGTH, full_ctag(c_to_cc(TAG)), ccs_cont00); \
    head_append(full_ctag(c_to_cc(TAG)), ccs_cont00); \
    get_forall_t<char>(); assert FORALLP_C; \
    get_forall_t<list<char> >(); assert FORALLP_CS; \
    if (!exists_t<char>(forallc, (valid_ctag)(head(full_ctag(c_to_cc(TAG)))))) \
    { \
      forall_t_elim(forallc, \
        (notf)((valid_ctag)(head(full_ctag(c_to_cc(TAG))))), TAG); \
      assert false; \
    } \
    SWITCH_TAG(TAG); \
    if (col) \
    { \
        crypto_chars_to_chars(P, SIZE); \
        public_chars(P, SIZE); \
        public_ccs_split(ccs00, TAG_LENGTH); \
        chars_to_secret_crypto_chars(P, SIZE); \
    } \
    switch(ccs00) {case cons(x00, xs00): case nil: assert false; }; \
    switch(nat_length(ccs00)) \
    { \
      case succ(n0): \
      case zero: \
        assert false; \
    } \
    assert true == well_formed_ccs(forallc, forallcs, nat_length(ccs00), ccs00); \
    close item_constraints(I, ccs00, pub); \
    leak item_constraints(I, ccs00, pub); \
  } \

lemma void well_formed_item_constraints(item i1, item i2);
  requires [_]item_constraints(i1, ?ccs, ?pub);
  ensures  [_]well_formed_item_ccs(i2)(ccs);

lemma void item_constraints_memcmp(item i);
  requires [_]item_constraints(i, ?ccs, ?pub);
  ensures  [_]memcmp_region(_, ccs);

lemma void item_constraints_deterministic(list<crypto_char> ccs1,
                                          list<crypto_char> ccs2, item i);
  requires true == well_formed_item(i) &*&
           [_]item_constraints(i, ccs1, ?pub) &*&
           [_]item_constraints(i, ccs2, pub);
  ensures  col || ccs1 == ccs2;

lemma void item_constraints_injective(item i1, item i2, list<crypto_char> ccs);
  requires [_]item_constraints(i1, ccs, ?pub) &*&
           [_]item_constraints(i2, ccs, pub);
  ensures  col || i1 == i2;

@*/

char item_tag(char* content, int size);
  /*@ requires [?f1]crypto_chars(secret, content, size, ?ccs) &*&
               [_]item_constraints(?i, ccs, ?pub) &*&
               [_]public_invar(polarssl_pub(pub)); @*/
  /*@ ensures  [f1]crypto_chars(secret, content, size, ccs) &*&
               result == tag_for_item(i) &*&
               head(ccs) == c_to_cc(result) &*&
               take(TAG_LENGTH, ccs) == full_ctag(head(ccs)); @*/

void ic_check_equal(char* cont1, int size1, char* cont2, int size2);
  /*@ requires [?f]world(?pub, ?key_clsfy) &*&
               principal(?principal, ?count) &*&
               [?f1]crypto_chars(secret, cont1, size1, ?ccs1) &*&
                 [_]item_constraints(?i1, ccs1, pub) &*&
               [?f2]crypto_chars(secret, cont2, size2, ?ccs2) &*&
                 [_]item_constraints(?i2, ccs2, pub); @*/
  /*@ ensures  [f]world(pub, key_clsfy) &*&
               principal(principal, count) &*&
               [f1]crypto_chars(secret, cont1, size1, ccs1) &*&
               [f2]crypto_chars(secret, cont2, size2, ccs2) &*&
               ccs1 == ccs2; @*/

#endif
