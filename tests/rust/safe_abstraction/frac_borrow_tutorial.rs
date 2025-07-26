// verifast_options{disable_overflow_check ignore_ref_creation ignore_unwind_paths}

fn add<'a>(r1: &'a i32, r2: &'a i32) -> i32
//@ req thread_token(?t) &*& [?qa]lifetime_token('a) &*& [_]frac_borrow('a, i32_full_borrow_content(t, r1)) &*& [_]frac_borrow('a, i32_full_borrow_content(t, r2));
//@ ens thread_token(t) &*& [qa]lifetime_token('a);
//@ safety_proof { assume(false); }
{
    //@ let f1 = open_frac_borrow('a, i32_full_borrow_content(t, r1), qa/2);
    //@ let f2 = open_frac_borrow('a, i32_full_borrow_content(t, r2), qa/2);
    let result = *r1 + *r2;
    //@ close_frac_borrow(f1, i32_full_borrow_content(t, r1));
    //@ close_frac_borrow(f2, i32_full_borrow_content(t, r2));
    result
}

fn double<'a>(r: &'a i32) -> i32
//@ req thread_token(?t) &*& [?qa]lifetime_token('a) &*& [_]frac_borrow('a, i32_full_borrow_content(t, r));
//@ ens thread_token(t) &*& [qa]lifetime_token('a);
//@ safety_proof { assume(false); }
{
    add/*@::<'a>@*/(r, r)
}

fn main()
//@ req thread_token(?t);
//@ ens thread_token(t);
{
    let mut x = 42;
    //@ let k = begin_lifetime();
    //@ borrow(k, i32_full_borrow_content(t, &x));
    //@ full_borrow_into_frac(k, i32_full_borrow_content(t, &x));
    let result;
    {
        //@ let_lft 'a = k;
        result = double/*@::<'a>@*/(&x);
    }
    //@ end_lifetime(k);
    //@ borrow_end(k, i32_full_borrow_content(t, &x));
    x = result;
    x -= 42;
}