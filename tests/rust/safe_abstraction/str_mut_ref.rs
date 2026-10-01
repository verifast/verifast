// Mutable string references (&mut str). Ownership is full_borrow('a, <str>.full_borrow_content(t, s)),
// where <str>.full_borrow_content is str_full_borrow_content: the bytes, which must be valid UTF-8.

fn test_mut_str<'a>(s: &'a mut str) -> &'a mut str
//@ req [?qa]lifetime_token('a) &*& full_borrow('a, <str>.full_borrow_content(currentThread, s));
//@ ens [qa]lifetime_token('a) &*& full_borrow('a, <str>.full_borrow_content(currentThread, result));
//@ on_unwind_ens false;
{
    s
}

// Opening the borrow exposes the bytes and their validity.
fn test_mut_str_open_close<'a>(s: &'a mut str)
//@ req thread_token(?t) &*& [?qa]lifetime_token('a) &*& full_borrow('a, <str>.full_borrow_content(t, s));
//@ ens thread_token(t) &*& [qa]lifetime_token('a);
//@ on_unwind_ens false;
{
    //@ open_full_borrow(qa, 'a, <str>.full_borrow_content(t, s));
    //@ open str_full_borrow_content(t, s)();
    //@ assert (s as *u8)[..s.len()] |-> ?bs &*& is_valid_utf8(bs) == true;
    //@ close str_full_borrow_content(t, s)();
    //@ close_full_borrow(<str>.full_borrow_content(t, s));
    //@ leak full_borrow(_, _);
}

// Default (generated) spec for a safe fn taking &'a mut str.
fn test_mut_str_default_spec<'a>(s: &'a mut str) -> usize {
    //@ leak full_borrow(_, _);
    s.len()
}

// A full borrow of a str place can be turned into a share of it. The generic lemma
// `share_full_borrow` does not apply to the unsized type `str`, so this is done by hand: the bytes
// go into a fractured borrow, and their validity is what `<str>.share` needs as well.
fn share_from_mut_str<'a>(s: &'a mut str) -> &'a str {
    //@ let t = currentThread;
    //@ open_full_borrow_strong_('a, <str>.full_borrow_content(t, s));
    //@ open str_full_borrow_content(t, s)();
    //@ let p = s as *u8;
    //@ assert array::<u8>(p, ?n, ?bs);
    //@ close mk_array::<u8>(p, n, bs)();
    /*@
    {
        pred Ctx() = true;
        produce_lem_ptr_chunk restore_full_borrow_(Ctx, mk_array::<u8>(p, n, bs), str_full_borrow_content(t, s))() {
            open Ctx();
            open mk_array::<u8>(p, n, bs)();
            close str_full_borrow_content(t, s)();
        } {
            close Ctx();
            close_full_borrow_strong_();
        }
    }
    @*/
    //@ full_borrow_into_frac('a, mk_array::<u8>(p, n, bs));
    //@ close exists(bs);
    //@ close str_share('a, t, s);
    //@ leak str_share('a, t, s);
    s
}

// Creating a &mut str from raw bytes, as `str::from_utf8_unchecked_mut` does, requires them to be valid UTF-8.
unsafe fn str_from_raw_parts_mut<'a>(p: *mut u8, n: usize) -> &'a mut str
//@ req thread_token(?t) &*& p[..n] |-> ?bs &*& is_valid_utf8(bs) == true;
//@ ens thread_token(t) &*& full_borrow('a, <str>.full_borrow_content(t, result)) &*& borrow_end_token('a, <str>.full_borrow_content(t, result));
{
    let s = std::ptr::slice_from_raw_parts_mut(p, n) as *mut str;
    //@ close str_full_borrow_content(t, s)();
    //@ borrow('a, <str>.full_borrow_content(t, s));
    &mut *s
}

// A &mut str parameter with an elided lifetime is an in-out parameter of the generated spec:
// the bytes and their validity before and after the call. Writes must keep the bytes valid UTF-8.
fn upcase_first_ascii(s: &mut str) {
    if s.len() > 0 {
        let p = s.as_mut_ptr();
        //@ open array(p, ?n, _);
        let b = unsafe { *p };
        if b'a' <= b && b <= b'z' {
            unsafe { *p = b - 32; }
        }
        //@ close array(p, n, _);
    }
}

// Negative tests.

/*@

// Closing the full borrow content of a str place requires the bytes to be valid UTF-8.
// (Calling this lemma makes VeriFast report the failure at the call site.)
lem close_str_full_borrow_content(t: thread_id_t, s: *str)
    req (s as *u8)[..s.len()] |-> ?bs &*& is_valid_utf8(bs) == true;
    ens str_full_borrow_content(t, s)();
{
    close str_full_borrow_content(t, s)();
}

@*/

fn close_with_invalid_byte<'a>(s: &'a mut str)
//@ req thread_token(?t) &*& [?qa]lifetime_token('a) &*& full_borrow('a, <str>.full_borrow_content(t, s));
//@ ens thread_token(t) &*& [qa]lifetime_token('a);
//@ on_unwind_ens false;
{
    //@ open_full_borrow(qa, 'a, <str>.full_borrow_content(t, s));
    //@ open str_full_borrow_content(t, s)();
    if s.len() > 0 {
        let p = s.as_mut_ptr();
        //@ open array(p, ?n, _);
        unsafe { *p = 0xFF; }
        //@ close array(p, n, _);
    }
    //@ close_str_full_borrow_content(t, s); //~should_fail
    //@ close_full_borrow(<str>.full_borrow_content(t, s));
    //@ leak full_borrow(_, _);
}

fn write_past_end(s: &mut str) {
    let p = s.as_mut_ptr();
    unsafe { *p.add(s.len()) = b'a'; } //~should_fail
}

// Checked last: an error in a generated postcondition leaves its call context behind, which
// would hide later //~should_fail locations.
fn write_invalid_byte(s: &mut str) { //~should_fail
    if s.len() > 0 {
        let p = s.as_mut_ptr();
        //@ open array(p, ?n, _);
        unsafe { *p = 0xFF; }
        //@ close array(p, n, _);
    }
}
