#ifndef GENERAL_GH
#define GENERAL_GH

#include "stdint.h"
//@ #include "lifetime_logic.gh"
/*@

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

predicate_ctor bool_full_borrow_content(thread_id_t t, bool *l)() = *l |-> ?_;
predicate_ctor char_full_borrow_content(thread_id_t t, uint32_t *l)() = *l |-> ?c &*& ((c >= 0 && c <= 0xD7FF) || (c >= 0xE000 && c <= 0x10FFFF));
predicate_ctor raw_ptr_full_borrow_content(thread_id_t t, void **l)() = *l |-> ?_;

predicate_ctor i8_full_borrow_content(thread_id_t t, int8_t *l)() = *l |-> ?_;
predicate_ctor i16_full_borrow_content(thread_id_t t, int16_t *l)() = *l |-> ?_;
predicate_ctor i32_full_borrow_content(thread_id_t t, int32_t *l)() = *l |-> ?_;
predicate_ctor i64_full_borrow_content(thread_id_t t, int64_t *l)() = *l |-> ?_;
predicate_ctor i128_full_borrow_content(thread_id_t t, int128_t *l)() = *l |-> ?_;
predicate_ctor isize_full_borrow_content(thread_id_t t, intptr_t *l)() = *l |-> ?_;

predicate_ctor u8_full_borrow_content(thread_id_t t, uint8_t *l)() = *l |-> ?_;
predicate_ctor u16_full_borrow_content(thread_id_t t, uint16_t *l)() = *l |-> ?_;
predicate_ctor u32_full_borrow_content(thread_id_t t, uint32_t *l)() = *l |-> ?_;
predicate_ctor u64_full_borrow_content(thread_id_t t, uint64_t *l)() = *l |-> ?_;
predicate_ctor u128_full_borrow_content(thread_id_t t, uint128_t *l)() = *l |-> ?_;
predicate_ctor usize_full_borrow_content(thread_id_t t, uintptr_t *l)() = *l |-> ?_;
@*/

#endif
