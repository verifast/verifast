fn main() {
    unsafe {
        let xs: [i32; 3] = [10, 20, 30];
        let mut sum = 0;
        let mut p: *const i32 = &raw const xs as *const i32;
        sum += *p;
        sum += *p.add(1);
        sum += *p.add(2);
        std::hint::assert_unchecked(sum == 60);
        //@ close [1/2]array_(p + 2, 1, _);
        //@ close [1/2]array_(p + 1, 2, _);
        //@ close [1/2]array_(p, 3, _);
    }
}
