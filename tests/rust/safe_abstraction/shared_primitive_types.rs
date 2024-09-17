fn bool_get<'a>(x: &'a bool) -> bool
{
    //@ open_frac_borrow('a, bool_full_borrow_content(_t, x), _q_a);
    //@ open [?qc]bool_full_borrow_content(_t, x)();
    let result = *x;
    //@ close [qc]bool_full_borrow_content(_t, x)();
    //@ close_frac_borrow(qc, bool_full_borrow_content(_t, x));
    result
}

fn char_get<'a>(x: &'a char) -> char
{
    //@ open_frac_borrow('a, char_full_borrow_content(_t, x), _q_a);
    //@ open [?qc]char_full_borrow_content(_t, x)();
    let result = *x;
    //@ open char_own(_t, result);
    //@ close char_own(_t, result);
    //@ close char_own(_t, result);
    //@ close [qc]char_full_borrow_content(_t, x)();
    //@ close_frac_borrow(qc, char_full_borrow_content(_t, x));
    result
}

fn raw_ptr_get<'a>(x: &'a *mut u8) -> *mut u8
{
    //@ open_frac_borrow('a, raw_ptr_full_borrow_content(_t, x), _q_a);
    //@ open [?qc]raw_ptr_full_borrow_content(_t, x)();
    let result = *x;
    //@ close [qc]raw_ptr_full_borrow_content(_t, x)();
    //@ close_frac_borrow(qc, raw_ptr_full_borrow_content(_t, x));
    result
}

fn i8_get<'a>(x: &'a i8) -> i8
{
    //@ open_frac_borrow('a, i8_full_borrow_content(_t, x), _q_a);
    //@ open [?qc]i8_full_borrow_content(_t, x)();
    let result = *x;
    //@ close [qc]i8_full_borrow_content(_t, x)();
    //@ close_frac_borrow(qc, i8_full_borrow_content(_t, x));
    result
}

fn i16_get<'a>(x: &'a i16) -> i16
{
    //@ open_frac_borrow('a, i16_full_borrow_content(_t, x), _q_a);
    //@ open [?qc]i16_full_borrow_content(_t, x)();
    let result = *x;
    //@ close [qc]i16_full_borrow_content(_t, x)();
    //@ close_frac_borrow(qc, i16_full_borrow_content(_t, x));
    result
}

fn i32_get<'a>(x: &'a i32) -> i32
{
    //@ open_frac_borrow('a, i32_full_borrow_content(_t, x), _q_a);
    //@ open [?qc]i32_full_borrow_content(_t, x)();
    let result = *x;
    //@ close [qc]i32_full_borrow_content(_t, x)();
    //@ close_frac_borrow(qc, i32_full_borrow_content(_t, x));
    result
}

fn i64_get<'a>(x: &'a i64) -> i64
{
    //@ open_frac_borrow('a, i64_full_borrow_content(_t, x), _q_a);
    //@ open [?qc]i64_full_borrow_content(_t, x)();
    let result = *x;
    //@ close [qc]i64_full_borrow_content(_t, x)();
    //@ close_frac_borrow(qc, i64_full_borrow_content(_t, x));
    result
}

fn i128_get<'a>(x: &'a i128) -> i128
{
    //@ open_frac_borrow('a, i128_full_borrow_content(_t, x), _q_a);
    //@ open [?qc]i128_full_borrow_content(_t, x)();
    let result = *x;
    //@ close [qc]i128_full_borrow_content(_t, x)();
    //@ close_frac_borrow(qc, i128_full_borrow_content(_t, x));
    result
}

fn u8_get<'a>(x: &'a u8) -> u8
{
    //@ open_frac_borrow('a, u8_full_borrow_content(_t, x), _q_a);
    //@ open [?qc]u8_full_borrow_content(_t, x)();
    let result = *x;
    //@ close [qc]u8_full_borrow_content(_t, x)();
    //@ close_frac_borrow(qc, u8_full_borrow_content(_t, x));
    result
}

fn u16_get<'a>(x: &'a u16) -> u16
{
    //@ open_frac_borrow('a, u16_full_borrow_content(_t, x), _q_a);
    //@ open [?qc]u16_full_borrow_content(_t, x)();
    let result = *x;
    //@ close [qc]u16_full_borrow_content(_t, x)();
    //@ close_frac_borrow(qc, u16_full_borrow_content(_t, x));
    result
}

fn u32_get<'a>(x: &'a u32) -> u32
{
    //@ open_frac_borrow('a, u32_full_borrow_content(_t, x), _q_a);
    //@ open [?qc]u32_full_borrow_content(_t, x)();
    let result = *x;
    //@ close [qc]u32_full_borrow_content(_t, x)();
    //@ close_frac_borrow(qc, u32_full_borrow_content(_t, x));
    result
}

fn u64_get<'a>(x: &'a u64) -> u64
{
    //@ open_frac_borrow('a, u64_full_borrow_content(_t, x), _q_a);
    //@ open [?qc]u64_full_borrow_content(_t, x)();
    let result = *x;
    //@ close [qc]u64_full_borrow_content(_t, x)();
    //@ close_frac_borrow(qc, u64_full_borrow_content(_t, x));
    result
}

fn u128_get<'a>(x: &'a u128) -> u128
{
    //@ open_frac_borrow('a, u128_full_borrow_content(_t, x), _q_a);
    //@ open [?qc]u128_full_borrow_content(_t, x)();
    let result = *x;
    //@ close [qc]u128_full_borrow_content(_t, x)();
    //@ close_frac_borrow(qc, u128_full_borrow_content(_t, x));
    result
}
