unsafe fn count_zeros(xs: *const i32, n: usize) -> usize
{
    let mut result: usize = 0;
    let r = std::ops::Range { start: 0, end: n };
    let mut it = r.into_iter();
    loop {
        let it_ref = &mut it;
        let i_opt = it_ref.next();
        match i_opt {
            None => break,
            Some(i) => {
                if *xs.add(i) == 0 {
                    result += 1;
                }
            }
        }
    }
    result
}
