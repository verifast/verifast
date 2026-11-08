pub fn test_casts_unops(x: i32, b: bool, p: *mut u32) -> (i32, bool, u64, i64, *const u8) {
    let neg = {
        let tmp = -x;
        tmp
    };
    let not_b = !b;
    let cast_u64 = x as u64;
    let cast_i64 = {
        let tmp = x as i64;
        tmp
    };
    let cast_ptr = p as *const u8;
    (neg, not_b, cast_u64, cast_i64, cast_ptr)
}

fn main() {}
