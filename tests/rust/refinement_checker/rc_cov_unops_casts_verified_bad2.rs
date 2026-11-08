pub fn test_casts_unops(x: i32, b: bool, p: *mut u32) -> (i32, bool, u64, i64, *const u8) {
    let neg = -x;
    let not_b = !b;
    let cast_u64 = (x as u16) as u64; // cast to wrong target width u16
    let cast_i64 = x as i64;
    let cast_ptr = p as *const u8;
    (neg, not_b, cast_u64, cast_i64, cast_ptr)
}

fn main() {}
