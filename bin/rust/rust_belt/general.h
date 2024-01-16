#ifndef GENERAL_GH
#define GENERAL_GH

#include "stdint.h"
//@ #include "lifetime_logic.gh"
/*@
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