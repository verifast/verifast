// Closing and opening `own` of 2- and 3-tuples from the components.
unsafe fn pair<'a, T>(a: &'a T, b: &'a T) -> (&'a T, &'a T)
//@ req thread_token(?t) &*& <&'a T>.own(t, a) &*& <&'a T>.own(t, b);
//@ ens thread_token(t) &*& <(&'a T, &'a T)>.own(t, result);
{
    let p = (a, b);
    //@ close_tuple_2_own(t, p);
    p
}

unsafe fn triple<'a, T>(a: &'a T, b: &'a T, c: &'a T) -> (&'a T, &'a T, &'a T)
//@ req thread_token(?t) &*& <&'a T>.own(t, a) &*& <&'a T>.own(t, b) &*& <&'a T>.own(t, c);
//@ ens thread_token(t) &*& <(&'a T, &'a T, &'a T)>.own(t, result);
{
    let p = (a, b, c);
    //@ close_tuple_3_own(t, p);
    p
}

unsafe fn first<'a, T>(p: (&'a T, &'a T)) -> &'a T
//@ req thread_token(?t) &*& <(&'a T, &'a T)>.own(t, p);
//@ ens thread_token(t) &*& <&'a T>.own(t, result);
{
    //@ open_tuple_2_own(t, p);
    //@ leak <&'a T>.own(t, p.1);
    p.0
}

fn main() {}
