fn bool_set<'a>(x: &'a mut bool, y: bool)
//@ req thread_token(?t) &*& [?q]lifetime_token(?a) &*& full_borrow(a, bool_full_borrow_content(t, x));
//@ ens thread_token(t) &*& [q]lifetime_token(a);
//@ on_unwind_ens false;
{
    //@ open_full_borrow(q, a, bool_full_borrow_content(t, x));
    //@ open bool_full_borrow_content(t, x)();
    *x = y;
    //@ close bool_full_borrow_content(t, x)();
    //@ close_full_borrow(bool_full_borrow_content(t, x));
    //@ leak full_borrow(_, _);
}

fn char_set<'a>(x: &'a mut char, y: char)
/*@ req thread_token(?t) &*& [?q]lifetime_token(?a) &*& full_borrow(a, char_full_borrow_content(t, x))
    &*& char_own(t, y);
@*/
//@ ens thread_token(t) &*& [q]lifetime_token(a);
//@ on_unwind_ens false;
{
    //@ open_full_borrow(q, a, char_full_borrow_content(t, x));
    //@ open char_full_borrow_content(t, x)();
    *x = y;
    //@ close char_full_borrow_content(t, x)();
    //@ close_full_borrow(char_full_borrow_content(t, x));
    //@ open char_own(t, _);
    //@ leak full_borrow(_, _);
}

fn raw_ptr_set<'a>(x: &'a mut *mut i32, y: *mut i32) {
    //@ open_full_borrow(_q_a, 'a, raw_ptr_full_borrow_content(_t, x));
    //@ open raw_ptr_full_borrow_content(_t, x)();
    *x = y;
    //@ close raw_ptr_full_borrow_content(_t, x)();
    //@ close_full_borrow(raw_ptr_full_borrow_content(_t, x));
    //@ leak full_borrow(_, _);
}

fn i8_set<'a>(x: &'a mut i8, y: i8)
//@ req thread_token(?t) &*& [?q]lifetime_token(?a) &*& full_borrow(a, i8_full_borrow_content(t, x));
//@ ens thread_token(t) &*& [q]lifetime_token(a);
//@ on_unwind_ens false;
{
    //@ open_full_borrow(q, a, i8_full_borrow_content(t, x));
    //@ open i8_full_borrow_content(t, x)();
    *x = y;
    //@ close i8_full_borrow_content(t, x)();
    //@ close_full_borrow(i8_full_borrow_content(t, x));
    //@ leak full_borrow(_, _);
}

fn i16_set<'a>(x: &'a mut i16, y: i16) {
    //@ open_full_borrow(_q_a, 'a, i16_full_borrow_content(_t, x));
    //@ open i16_full_borrow_content(_t, x)();
    *x = y;
    //@ close i16_full_borrow_content(_t, x)();
    //@ close_full_borrow(i16_full_borrow_content(_t, x));
    //@ leak full_borrow(_, _);
}

fn i32_set<'a>(x: &'a mut i32, y: i32) {
    //@ open_full_borrow(_q_a, 'a, i32_full_borrow_content(_t, x));
    //@ open i32_full_borrow_content(_t, x)();
    *x = y;
    //@ close i32_full_borrow_content(_t, x)();
    //@ close_full_borrow(i32_full_borrow_content(_t, x));
    //@ leak full_borrow(_, _);
}

fn i64_set<'a>(x: &'a mut i64, y: i64) {
    //@ open_full_borrow(_q_a, 'a, i64_full_borrow_content(_t, x));
    //@ open i64_full_borrow_content(_t, x)();
    *x = y;
    //@ close i64_full_borrow_content(_t, x)();
    //@ close_full_borrow(i64_full_borrow_content(_t, x));
    //@ leak full_borrow(_, _);
}

fn i128_set<'a>(x: &'a mut i128, y: i128) {
    //@ open_full_borrow(_q_a, 'a, i128_full_borrow_content(_t, x));
    //@ open i128_full_borrow_content(_t, x)();
    *x = y;
    //@ close i128_full_borrow_content(_t, x)();
    //@ close_full_borrow(i128_full_borrow_content(_t, x));
    //@ leak full_borrow(_, _);
}

fn isize_set<'a>(x: &'a mut isize, y: isize) {
    //@ open_full_borrow(_q_a, 'a, isize_full_borrow_content(_t, x));
    //@ open isize_full_borrow_content(_t, x)();
    *x = y;
    //@ close isize_full_borrow_content(_t, x)();
    //@ close_full_borrow(isize_full_borrow_content(_t, x));
    //@ leak full_borrow(_, _);
}

fn u8_set<'a>(x: &'a mut u8, y: u8) {
    //@ open_full_borrow(_q_a, 'a, u8_full_borrow_content(_t, x));
    //@ open u8_full_borrow_content(_t, x)();
    *x = y;
    //@ close u8_full_borrow_content(_t, x)();
    //@ close_full_borrow(u8_full_borrow_content(_t, x));
    //@ leak full_borrow(_, _);
}

fn u16_set<'a>(x: &'a mut u16, y: u16) {
    //@ open_full_borrow(_q_a, 'a, u16_full_borrow_content(_t, x));
    //@ open u16_full_borrow_content(_t, x)();
    *x = y;
    //@ close u16_full_borrow_content(_t, x)();
    //@ close_full_borrow(u16_full_borrow_content(_t, x));
    //@ leak full_borrow(_, _);
}

fn u32_set<'a>(x: &'a mut u32, y: u32) {
    //@ open_full_borrow(_q_a, 'a, u32_full_borrow_content(_t, x));
    //@ open u32_full_borrow_content(_t, x)();
    *x = y;
    //@ close u32_full_borrow_content(_t, x)();
    //@ close_full_borrow(u32_full_borrow_content(_t, x));
    //@ leak full_borrow(_, _);
}

fn u64_set<'a>(x: &'a mut u64, y: u64) {
    //@ open_full_borrow(_q_a, 'a, u64_full_borrow_content(_t, x));
    //@ open u64_full_borrow_content(_t, x)();
    *x = y;
    //@ close u64_full_borrow_content(_t, x)();
    //@ close_full_borrow(u64_full_borrow_content(_t, x));
    //@ leak full_borrow(_, _);
}

fn u128_set<'a>(x: &'a mut u128, y: u128) {
    //@ open_full_borrow(_q_a, 'a, u128_full_borrow_content(_t, x));
    //@ open u128_full_borrow_content(_t, x)();
    *x = y;
    //@ close u128_full_borrow_content(_t, x)();
    //@ close_full_borrow(u128_full_borrow_content(_t, x));
    //@ leak full_borrow(_, _);
}

fn usize_set<'a>(x: &'a mut usize, y: usize) {
    //@ open_full_borrow(_q_a, 'a, usize_full_borrow_content(_t, x));
    //@ open usize_full_borrow_content(_t, x)();
    *x = y;
    //@ close usize_full_borrow_content(_t, x)();
    //@ close_full_borrow(usize_full_borrow_content(_t, x));
    //@ leak full_borrow(_, _);
}

fn triggers_verification<'a>(x: &'a mut i32) {
    //@ open_full_borrow(_q_a, 'a, i32_full_borrow_content(_t, x));
    //@ open i32_full_borrow_content(_t, x)();
    let y = unsafe { *(x as *const i32) };
    //@ close i32_full_borrow_content(_t, x)();
    //@ close_full_borrow(i32_full_borrow_content(_t, x));
    //@ leak full_borrow(_, _);
}
