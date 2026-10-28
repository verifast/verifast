// `<[T; N]>.share` and `<[T; N]>.full_borrow_content` of a literal-length array.

unsafe fn shared<'a>(a: &'a [u8; 4]) -> &'a [u8; 4]
//@ req [_](<[u8; 4]>.share('a, ?t, a));
//@ ens [_](<[u8; 4]>.share('a, t, result));
{
    a
}

unsafe fn borrowed<'a>(a: &'a mut [u8; 4])
//@ req thread_token(?t) &*& [?q]lifetime_token('a) &*& full_borrow('a, <[u8; 4]>.full_borrow_content(t, a));
//@ ens thread_token(t) &*& [q]lifetime_token('a);
{
    //@ open_full_borrow(q, 'a, <[u8; 4]>.full_borrow_content(t, a));
    //@ open Array_full_borrow_content::<u8, 4>(t, a)();
    //@ assert (a as *u8)[..int_of_const(typeid(4))] |-> ?elems;
    //@ close Array_full_borrow_content::<u8, 4>(t, a)();
    //@ close_full_borrow(<[u8; 4]>.full_borrow_content(t, a));
    //@ leak full_borrow(_, _);
}

fn main() {}
