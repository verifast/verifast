unsafe fn count_zeros(xs: *const i32, n: usize) -> usize {
    let mut result: usize = 0;
    for i in 0..n {
        if *xs.add(i) == 0 {
            result += 1;
        }
    }
    result
}
