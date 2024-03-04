#ifndef GENERAL_GH
#define GENERAL_GH

#include "stdint.h"
//@ #include "lifetime_logic.gh"
/*@

predicate atomic_mask(mask_t mask);
predicate atomic_space(mask_t mask, predicate() inv;);

lemma void create_atomic_space(mask_t mask, predicate() inv);
    requires !mask_is_empty(mask) &*& inv();
    ensures atomic_space(mask, inv);

lemma void open_atomic_space(mask_t spaceMask, predicate() inv);
    requires [?f]atomic_space(spaceMask, inv) &*& atomic_mask(?currentMask) &*& mask_le(spaceMask, currentMask) == true;
    ensures [f]atomic_space(spaceMask, inv) &*& atomic_mask(mask_diff(currentMask, spaceMask)) &*& inv();

lemma void close_atomic_space(mask_t spaceMask, predicate() inv);
    requires [?f]atomic_space(spaceMask, inv) &*& atomic_mask(?currentMask) &*& inv();
    ensures [f]atomic_space(spaceMask, inv) &*& atomic_mask(mask_union(currentMask, spaceMask));

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
@*/

#endif
