// A &mut [T] parameter with an elided lifetime, of a function whose return type has no elided lifetimes,
// is an in-out parameter of the generated spec: the elements and their ownership before and after the
// call, that is, the body of <[T]>.full_borrow_content (slice_full_borrow_content).

// The example from issue #997.
fn test(buf: &mut [u8]) -> u32 {
    return 0;
}

// The in-out resources are exactly the body of slice_full_borrow_content.
fn in_out_is_full_borrow_content<T>(s: &mut [T]) {
    //@ close slice_full_borrow_content::<T>(currentThread, s)();
    //@ open slice_full_borrow_content::<T>(currentThread, s)();
}

fn in_out_is_full_borrow_content_u8(s: &mut [u8]) {
    //@ close slice_full_borrow_content::<u8>(currentThread, s)();
    //@ open slice_full_borrow_content::<u8>(currentThread, s)();
}

fn read_first(s: &mut [u8]) -> u8 {
    if s.len() == 0 {
        return 0;
    }
    let p = s as *mut [u8] as *mut u8;
    //@ open array(p, ?n, ?bs);
    let b = unsafe { *p };
    //@ close array(p, n, bs);
    b
}

fn set_first(s: &mut [u8]) {
    if s.len() > 0 {
        let p = s as *mut [u8] as *mut u8;
        //@ open array(p, ?n, ?bs);
        unsafe { *p = 1; }
        //@ close array(p, n, cons(1 as u8, tail(bs)));
        //@ open foreach(bs, own::<u8>(currentThread));
        //@ leak own::<u8>(currentThread)(head(bs));
        //@ close u8_own(currentThread, 1);
        //@ close own::<u8>(currentThread)(1);
        //@ close foreach(cons(1 as u8, tail(bs)), own::<u8>(currentThread));
    }
}

fn swap_first_two<T>(s: &mut [T]) {
    if s.len() >= 2 {
        let p = s as *mut [T] as *mut T;
        //@ open array(p, ?n, ?elems);
        //@ open array(p + 1, n - 1, tail(elems));
        unsafe {
            let a = std::ptr::read(p);
            let b = std::ptr::read(p.add(1));
            std::ptr::write(p, b);
            std::ptr::write(p.add(1), a);
        }
        //@ close array(p + 1, n - 1, cons(head(elems), tail(tail(elems))));
        //@ close array(p, n, cons(head(tail(elems)), cons(head(elems), tail(tail(elems)))));
        //@ open foreach(elems, own::<T>(currentThread));
        //@ open foreach(tail(elems), own::<T>(currentThread));
        //@ close foreach(cons(head(elems), tail(tail(elems))), own::<T>(currentThread));
        //@ close foreach(cons(head(tail(elems)), cons(head(elems), tail(tail(elems)))), own::<T>(currentThread));
    }
}

// A caller passes the elements and their ownership, and gets them back.
unsafe fn caller<'a>(s: &'a mut [u8], v: &'a mut [i32])
//@ req thread_token(?t) &*& t == currentThread &*& [?q]lifetime_token('a) &*& array::<u8>(s as *u8, s.len(), ?bs) &*& foreach(bs, own::<u8>(t)) &*& array::<i32>(v as *i32, v.len(), ?vs) &*& foreach(vs, own::<i32>(t));
//@ ens thread_token(t) &*& [q]lifetime_token('a) &*& array::<u8>(s as *u8, s.len(), ?bs1) &*& foreach(bs1, own::<u8>(t)) &*& array::<i32>(v as *i32, v.len(), ?vs1) &*& foreach(vs1, own::<i32>(t));
//@ on_unwind_ens thread_token(t) &*& [q]lifetime_token('a) &*& array::<u8>(s as *u8, s.len(), ?bs1) &*& foreach(bs1, own::<u8>(t)) &*& array::<i32>(v as *i32, v.len(), ?vs1) &*& foreach(vs1, own::<i32>(t));
{
    set_first/*@::<'a>@*/(s);
    swap_first_two/*@::<u8, 'a>@*/(s);
    swap_first_two/*@::<i32, 'a>@*/(v);
}

// Negative tests.

fn write_past_end(s: &mut [u8]) {
    let p = s as *mut [u8] as *mut u8;
    unsafe { *p.add(s.len()) = 1; } //~should_fail
}

// The following fail at the generated postcondition, so they come last.

// The postcondition is about the elements of the slice that was passed in, even if the callee
// assigns a shorter slice to its parameter.
fn shrink(mut s: &mut [u8]) { //~should_fail
    if s.len() > 1 {
        let p = s as *mut [u8] as *mut u8;
        let q = std::ptr::slice_from_raw_parts_mut(p, 1);
        s = unsafe { &mut *q };
        //@ open array(p, ?n, ?bs);
        //@ leak array(p + 1, n - 1, _);
        //@ open foreach(bs, own::<u8>(currentThread));
        //@ leak foreach(tail(bs), own::<u8>(currentThread));
        //@ close array(p + 1, 0, nil);
        //@ close array(p, 1, cons(head(bs), nil));
        //@ close foreach(nil, own::<u8>(currentThread));
        //@ close foreach(cons(head(bs), nil), own::<u8>(currentThread));
    }
}

// Dropping an element without replacing it would make the caller drop it again.
fn drop_first<T>(s: &mut [T]) { //~should_fail
    if s.len() > 0 {
        let p = s as *mut [T] as *mut T;
        //@ open array(p, ?n, ?elems);
        let x = unsafe { std::ptr::read(p) };
        //@ close array(p, n, elems);
        //@ open foreach(elems, own::<T>(currentThread));
        //@ open own::<T>(currentThread)(head(elems));
        drop(x);
    }
}
