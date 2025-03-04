fn my_replace(r: &mut i32, v: i32) -> i32 {
    std::mem::replace(r, { *r; v })
}
