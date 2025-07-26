// verifast_options{disable_overflow_check ignore_unwind_paths}

fn increment<'a>(r: &'a mut i32)
//@ req thread_token(?t) &*& [?qa]lifetime_token('a) &*& full_borrow('a, <i32>.full_borrow_content(t, r));
//@ ens thread_token(t) &*& [qa]lifetime_token('a);
//@ safety_proof { assume(false); }
{
    //@ open_full_borrow(qa, 'a, <i32>.full_borrow_content(t, r));
    //@ open i32_full_borrow_content(t, r)();
    *r += 1;
    //@ close i32_full_borrow_content(t, r)();
    //@ close_full_borrow(<i32>.full_borrow_content(t, r));
    //@ leak full_borrow('a, <i32>.full_borrow_content(t, r));
}

fn main()
//@ req thread_token(?t);
//@ ens thread_token(t);
{
    let mut x = 83;
    //@ let k = begin_lifetime();
    //@ close i32_full_borrow_content(t, &x)();
    //@ borrow(k, i32_full_borrow_content(t, &x));
    {
        //@ let_lft 'a = k;
        increment/*@::<'a>@*/(&mut x);
    }
    //@ end_lifetime(k);
    //@ borrow_end(k, i32_full_borrow_content(t, &x));
    //@ open i32_full_borrow_content(t, &x)();
    x -= 42;
    //println!("The answer is {}", x);
}
