/*@

fix count_zeros_pure(xs: list<i32>) -> i32 {
    match xs {
        nil => 0,
        cons(x, xs0) => if x == 0 { 1 } else { 0 } + count_zeros_pure(xs0)
    }
}

@*/

unsafe fn count_zeros(xs: *const i32, n: usize) -> usize
//@ req xs[..n] |-> ?vs;
//@ ens xs[..n] |-> vs &*& result == count_zeros_pure(vs);
//@ on_unwind_ens false;
{
    let mut result: usize = 0;
    let r = std::ops::Range { start: 0, end: n };
    let mut it = r.into_iter();
    loop {
        /*@
        req it |-> ?r0 &*& r0.end == n &*& xs[r0.start..n] |-> ?vs1 &*& result <= r0.start;
        ens it |-> _ &*& xs[r0.start..n] |-> vs1 &*& result - old_result == count_zeros_pure(vs1);
        @*/
        //@ open array(_, _, _);
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
