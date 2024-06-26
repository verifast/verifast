#ifndef GENERAL_GH
#define GENERAL_GH

#include "stdint.h"
//@ #include "lifetime_logic.gh"
//@ #include "counting.gh"
//@ #include "ghost_cells.gh"

/*
Iris View Shifts

In Iris, the mask mechanism prevents one from re-opening an invariant and duplicating its resources. Mask-changing view shifts which reduce the mask,
imply the possibility of opened invariants in the state after the view shift. So, mask-changing view shifts can just be used
in the context of the proof for a triple around an atomic expression (see HOARE-VS-ATOMIC) or another view shift (VS-TRANS).
let us call these contexts atomic contexts.

Mask-preserving view shifts, on the other hand, imply that in the proof of the view shift an invariant under the mask might have been opened and closed,
i.e. the mask is needed but no newly opened invariant after the view shift.
Mask-preserving view shifts are allowed around any Hoare triple with the same mask (see HOARE-VS).

Here, in VeriFast, view shifts are represented as lemmas. To represent Iris's rules our design needs the following properties:
1- All forms of view shifts cannot be used when their mask is not available.
2- Mask-changing view shifts are only allowed in atomic contexts

To spare users some burden when working with mask-preserving view shifts in non-atomic contexts, the mechanism is as follows:
a- Mask-preserving view shifts are represented as a pair of lemmas:
    - First a `nonghost_callers_only` lemma without any notion of mask in its contract. Intuitively, we assume an imaginary `mask(Top)` token is provided
    at the beginning of the verification of each function. A mask-preserving view shift can be satisfied as we always have all masks available.
    No other view shift has opened any mask because mask-changing ones are not applicable here as we will see soon.
    These maskless lemmas are not usable in an atomic context where a mask might have been opened because those contexts are all ghost contexts.
    - Second, another mask-aware version of the lemma with specs like `req atomic_mask(Nlft) ...; ens atomic_mask(Nlft);` which is not `nonghost_callers_only`.
    These are usable in atomic contexts where masks might have been opened. In such a context, `atomic_mask(m)` tokens are provided,
    showing the mask `m` is available and witnessing we are in an atomic context at the same time. As mentioned earlier,
    these mask-aware lemmas are not usable in real function bodies as there is no explicit `atomic_mask(m)` available there.
b- Mask-changing view shifts will only have the second form naturally.
*/

/*@
predicate atomic_space(mask_t mask, predicate() inv;);
/* This would be the existentially quantified `R` in the derived rule on Ralf Jung's thesis in the middle of page 67.
See https://research.ralfj.de/phd/thesis-screen.pdf */
predicate close_atomic_space_token(mask_t spaceMask, predicate() inv);

lemma void create_atomic_space(mask_t mask, predicate() inv);
    requires !mask_is_empty(mask) &*& inv();
    ensures atomic_space(mask, inv);

lemma void open_atomic_space(mask_t spaceMask, predicate() inv);
    requires [?f]atomic_space(spaceMask, inv) &*& atomic_mask(?currentMask) &*& mask_le(spaceMask, currentMask) == true;
    ensures [f]atomic_space(spaceMask, inv) &*& atomic_mask(mask_diff(currentMask, spaceMask))
            &*& close_atomic_space_token(spaceMask, inv) &*& inv();

lemma void close_atomic_space(mask_t spaceMask);
    requires atomic_mask(?currentMask) &*& close_atomic_space_token(spaceMask, ?inv) &*& inv();
    ensures atomic_mask(mask_union(currentMask, spaceMask));

typedef lemma void atomic_block(predicate() pre, predicate() post)();
    requires atomic_mask(MaskTop) &*& pre();
    ensures atomic_mask(MaskTop) &*& post();

lemma void perform_atomically();
    nonghost_callers_only
    requires is_atomic_block(?block, ?pre, ?post) &*& pre();
    ensures is_atomic_block(block, pre, post) &*& post();

predicate_ctor simple_share(fixpoint(thread_id_t, void *, predicate(;)) frac_borrow_content)(lifetime_t k, thread_id_t t, void *l) =
    frac_borrow(k, frac_borrow_content(t, l));
predicate_ctor shared_ref_own(predicate(lifetime_t, thread_id_t, void *) pointee_shr, lifetime_t k)(thread_id_t t, void *l) = [_]pointee_shr(k, t, l);

predicate na_inv(thread_id_t t, mask_t m, predicate() p);
//NAInv-new-inv
lemma void na_inv_new(thread_id_t t, mask_t m, predicate() p);
    nonghost_callers_only
    requires p();
    ensures [_]na_inv(t, m, p);
//NAInv-acc
predicate close_na_inv_token(thread_id_t t, mask_t m, predicate() p);
lemma void open_na_inv(thread_id_t t, mask_t m, predicate() p);
    nonghost_callers_only
    requires [_]na_inv(t, m, p) &*& partial_thread_token(t, ?m0) &*& mask_le(m, m0) == true;
    ensures partial_thread_token(t, mask_diff(m0, m)) &*& p() &*& close_na_inv_token(t, m, p);

lemma void close_na_inv(thread_id_t t, mask_t m);
    nonghost_callers_only
    requires close_na_inv_token(t, m, ?p) &*& p();
    ensures partial_thread_token(t, m);

//Mask preserving view-shifts. Mask aware versions
//NAInv-new-inv
lemma void na_inv_new_m(thread_id_t t, mask_t m, predicate() p);
    requires atomic_mask(?m0) &*& mask_le(m, m0) == true &*& p();
    ensures atomic_mask(m0) &*& [_]na_inv(t, m, p);

lemma void open_na_inv_m(thread_id_t t, mask_t m, predicate() p);
    requires atomic_mask(?am0) &*& mask_le(m, am0) == true &*& [_]na_inv(t, m, p) &*& partial_thread_token(t, ?m0) &*& mask_le(m, m0) == true;
    ensures atomic_mask(am0) &*& partial_thread_token(t, mask_diff(m0, m)) &*& p() &*& close_na_inv_token(t, m, p);

lemma void close_na_inv_m(thread_id_t t, mask_t m);
    requires atomic_mask(?am0) &*& mask_le(m, am0) == true &*& close_na_inv_token(t, m, ?p) &*& p();
    ensures atomic_mask(am0) &*& partial_thread_token(t, m);

predicate bool_own(thread_id_t t, bool v;) = true;
predicate char_own(thread_id_t t, uint32_t v;) = 0 <= v && v <= 0xD7FF || 0xE000 <= v && v <= 0x10FFFF;
predicate raw_ptr_own(thread_id_t t, void *v;) = true;

predicate i8_own(thread_id_t t, int8_t v;) = true;
predicate i16_own(thread_id_t t, int16_t v;) = true;
predicate i32_own(thread_id_t t, int32_t v;) = true;
predicate i64_own(thread_id_t t, int64_t v;) = true;
predicate i128_own(thread_id_t t, int128_t v;) = true;
predicate isize_own(thread_id_t t, intptr_t v;) = true;

predicate u8_own(thread_id_t t, uint8_t v;) = true;
predicate u16_own(thread_id_t t, uint16_t v;) = true;
predicate u32_own(thread_id_t t, uint32_t v;) = true;
predicate u64_own(thread_id_t t, uint64_t v;) = true;
predicate u128_own(thread_id_t t, uint128_t v;) = true;
predicate usize_own(thread_id_t t, uintptr_t v;) = true;

predicate_ctor bool_full_borrow_content(thread_id_t t, bool *l)(;) = *l |-> ?_;
predicate_ctor char_full_borrow_content(thread_id_t t, uint32_t *l)(;) = *l |-> ?c &*& char_own(t, c);
predicate_ctor raw_ptr_full_borrow_content(thread_id_t t, void **l)(;) = *l |-> ?_;

predicate_ctor i8_full_borrow_content(thread_id_t t, int8_t *l)(;) = *l |-> ?_;
predicate_ctor i16_full_borrow_content(thread_id_t t, int16_t *l)(;) = *l |-> ?_;
predicate_ctor i32_full_borrow_content(thread_id_t t, int32_t *l)(;) = *l |-> ?_;
predicate_ctor i64_full_borrow_content(thread_id_t t, int64_t *l)(;) = *l |-> ?_;
predicate_ctor i128_full_borrow_content(thread_id_t t, int128_t *l)(;) = *l |-> ?_;
predicate_ctor isize_full_borrow_content(thread_id_t t, intptr_t *l)(;) = *l |-> ?_;

predicate_ctor u8_full_borrow_content(thread_id_t t, uint8_t *l)(;) = *l |-> ?_;
predicate_ctor u16_full_borrow_content(thread_id_t t, uint16_t *l)(;) = *l |-> ?_;
predicate_ctor u32_full_borrow_content(thread_id_t t, uint32_t *l)(;) = *l |-> ?_;
predicate_ctor u64_full_borrow_content(thread_id_t t, uint64_t *l)(;) = *l |-> ?_;
predicate_ctor u128_full_borrow_content(thread_id_t t, uint128_t *l)(;) = *l |-> ?_;
predicate_ctor usize_full_borrow_content(thread_id_t t, uintptr_t *l)(;) = *l |-> ?_;

type_pred_decl predicate(thread_id_t, Self) <Self>.own;
type_pred_decl fixpoint(thread_id_t, void *, predicate()) <Self>.full_borrow_content;
type_pred_decl predicate(lifetime_t, thread_id_t, void *) <Self>.share;

predicate_ctor own<T>(thread_id_t t)(T v) = (<T>.own)(t, v);

type_pred_def <bool>.own = bool_own;
//TODO: How to deal with Rust type `char`? Distinct Rust types should be mapped to distinct VF types, with distinct typeids.
type_pred_def <void *>.own = raw_ptr_own;

type_pred_def <int8_t>.own = i8_own;
type_pred_def <int16_t>.own = i16_own;
type_pred_def <int32_t>.own = i32_own;
type_pred_def <int64_t>.own = i64_own;
type_pred_def <int128_t>.own = i128_own;
type_pred_def <intptr_t>.own = isize_own;

type_pred_def <uint8_t>.own = u8_own;
type_pred_def <uint16_t>.own = u16_own;
type_pred_def <uint32_t>.own = u32_own;
type_pred_def <uint64_t>.own = u64_own;
type_pred_def <uint128_t>.own = u128_own;
type_pred_def <uintptr_t>.own = usize_own;

lemma void open_full_borrow_content<T>(thread_id_t t, T *l);
    requires ((<T>.full_borrow_content)(t, l))();
    ensures *l |-> ?v &*& (<T>.own)(t, v);

lemma void close_full_borrow_content<T>(thread_id_t t, T *l);
    requires *l |-> ?v &*& (<T>.own)(t, v);
    ensures ((<T>.full_borrow_content)(t, l))();

fixpoint int type_depth(void *typeId);

predicate type_interp<T>(;) = ghost_rec_perm(type_depth(typeid(T)));

lemma void share_mono<T>(lifetime_t k, lifetime_t k1, thread_id_t t, T *l);
    requires type_interp<T>() &*& lifetime_inclusion(k1, k) == true &*& [_](<T>.share)(k, t, l);
    ensures type_interp<T>() &*& [_](<T>.share)(k1, t, l);

lemma void share_full_borrow<T>(lifetime_t k, thread_id_t t, void *l);
    nonghost_callers_only
    requires type_interp<T>() &*& full_borrow(k, (<T>.full_borrow_content)(t, l)) &*& [?q]lifetime_token(k);
    ensures type_interp<T>() &*& [_](<T>.share)(k, t, l) &*& [q]lifetime_token(k);

lemma void share_full_borrow_m<T>(lifetime_t k, thread_id_t t, void *l);
    requires type_interp<T>() &*& atomic_mask(?mask) &*& mask_le(Nlft, mask) == true &*& full_borrow(k, (<T>.full_borrow_content)(t, l)) &*& [?q]lifetime_token(k);
    ensures type_interp<T>() &*& atomic_mask(mask) &*& [_](<T>.share)(k, t, l) &*& [q]lifetime_token(k);

fixpoint bool is_Send(void *type_id);

lemma void Send::send<T>(thread_id_t t0, thread_id_t t1, T v);
    requires type_interp<T>() &*& is_Send(typeid(T)) == true &*& (<T>.own)(t0, v);
    ensures type_interp<T>() &*& (<T>.own)(t1, v);

predicate lifetimes(list<lifetime_t> lifetimes) = true; // Serves only to carry a function call's lifetime arguments.

@*/

#endif
