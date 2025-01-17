/*@

pred foo(b: bool) = true;

pred bar(x: *i32, y: *i32) = foo(?b) &*& if b { *x |-> _ } else { *y |-> _ };

lem merge_bar() // This lemma is false!
    req [?f1]bar(?x, ?y) &*& [?f2]bar(x, y);
    ens [f1 + f2]bar(x, y);
{
    assume(false);
}

@*/

fn main() {
    unsafe {
        let mut x = 42;
        let mut y = 42;
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
