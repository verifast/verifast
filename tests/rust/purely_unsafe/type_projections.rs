// verifast_options{ignore_ref_creation disable_overflow_check}

unsafe fn call_fnonce<F: FnOnce()>(f: F)
//@ req thread_token(?t) &*& <F>.own(t, f);
//@ ens thread_token(t);
//@ on_unwind_ens thread_token(t);
{
    //@ close_tuple_0_own(t);
    f();
    //@ open_tuple_0_own(t);
}

unsafe fn call_fnmut<F: FnMut()>(f: &mut F)
//@ req thread_token(?t) &*& *f |-> ?f0 &*& <F>.own(t, f0);
//@ ens thread_token(t) &*& *f |-> ?f1 &*& <F>.own(t, f1);
//@ on_unwind_ens thread_token(t) &*& *f |-> ?f1 &*& <F>.own(t, f1);
{
    //@ close_tuple_0_own(t);
    f();
    //@ open_tuple_0_own(t);
}

unsafe fn call_fn<'a, F: Fn()>(f: &'a F)
//@ req thread_token(?t) &*& [?q]lifetime_token('a) &*& [_](<F>.share('a, t, f));
//@ ens thread_token(t) &*& [q]lifetime_token('a);
//@ on_unwind_ens thread_token(t) &*& [q]lifetime_token('a);
{
    //@ close_tuple_0_own(t);
    f/*@::<F, (), 'a>@*/();
    //@ open_tuple_0_own(t);
}

unsafe fn sum<I: Iterator<Item = usize>>(i: &mut I) -> usize
//@ req thread_token(?t) &*& *i |-> ?i0 &*& <I>.own(t, i0);
//@ ens thread_token(t) &*& *i |-> ?i1 &*& <I>.own(t, i1);
//@ on_unwind_ens thread_token(t) &*& *i |-> ?i1 &*& <I>.own(t, i1);
{
    let mut result = 0;
    loop {
        //@ inv thread_token(t) &*& *i |-> ?i1 &*& <I>.own(t, i1);
        
        match i.next() {
            None => {
                //@ leak <std::option::Option<usize>>.own(_, _);
                return result;
            }
            Some(v) => {
                //@ leak <std::option::Option<usize>>.own(_, _);
                result += v;
            }
        }
    }
}