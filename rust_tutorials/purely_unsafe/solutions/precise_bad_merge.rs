/*@

pred foo(b: bool) = true;

pred bar(x: *mut i32, y: *mut i32) =
    foo(?b) &*& if b { *x |-> 0 } else { *y |-> 0 };

lem merge_bar() // This lemma is false!!
    req [?f1]bar(?x, ?y) &*& [?f2]bar(x, y);
    ens [f1 + f2]bar(x, y);
{
    assume(false);
}

@*/

fn main()
//@ req true;
//@ ens true;
{
    unsafe {
        let mut x = 0;
        let mut y = 0;
        //@ close [1/2]foo(true);
        //@ close [1/2]bar(&x, &y);
        //@ close [1/2]foo(false);
        //@ close [1/2]bar(&x, &y);
        //@ merge_bar();
        //@ open bar(&x, &y);
        //@ assert foo(?b);
        //@ if b { points_to_limits(&x); } else { points_to_limits(&y); }
        std::hint::unreachable_unchecked();
    }
}
