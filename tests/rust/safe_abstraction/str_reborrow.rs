// Reborrowing a shared string reference (`&*s` with `s: &str`, also inserted implicitly by method
// calls such as `s.len()`) is translated to a call of `reborrow_str_ref` (see bin/rust/aliasing.rsspec).
// Like `reborrow_slice_ref`, it returns the same reference and produces no permissions.

// Default (generated) spec; `s.len()` reborrows `s`.
fn str_len(s: &str) -> usize {
    s.len()
}

// The result of a reborrow is the reference itself, so the caller's share of `s` is a share of the result.
fn reborrow_explicit<'a>(s: &'a str) -> &'a str
//@ req [?qa]lifetime_token('a) &*& [_](<str>.share('a, currentThread, s));
//@ ens [qa]lifetime_token('a) &*& [_](<str>.share('a, currentThread, result)) &*& result == s;
//@ on_unwind_ens false;
{
    &*s
}

// Reading through a reborrowed reference uses the caller's permission for the bytes of `s`.
unsafe fn first_byte(s: &str) -> u8
//@ req [?f](s as *u8)[..s.len()] |-> ?bs &*& 0 < s.len();
//@ ens [f](s as *u8)[..s.len()] |-> bs &*& result == head(bs);
{
    let t: &str = &*s;
    //@ open array(_, _, _);
    let b = *t.as_ptr();
    //@ close [f]array(s as *u8, s.len(), bs);
    b
}

// Negative tests: a reborrow does not produce any permission that the caller did not have.

// It does not produce a share of the string.
fn reborrow_no_share<'a>(s: &'a str) -> &'a str
//@ req [?qa]lifetime_token('a);
//@ ens [qa]lifetime_token('a) &*& [_](<str>.share('a, currentThread, result)); //~should_fail
//@ on_unwind_ens false;
{
    &*s
}

// It does not produce permission to read the bytes.
unsafe fn read_without_permission(s: &str) -> u8
//@ req 0 < s.len();
//@ ens true;
{
    let t: &str = &*s;
    *t.as_ptr() //~should_fail
}

// It does not turn a fraction of the bytes into permission to write them.
unsafe fn write_through_reborrow(s: &str)
//@ req [1/2](s as *u8)[..s.len()] |-> ?bs &*& 0 < s.len();
//@ ens [1/2](s as *u8)[..s.len()] |-> bs;
{
    let t: &str = &*s;
    let p = t.as_ptr() as *mut u8;
    //@ open array(_, _, _);
    *p = b'a'; //~should_fail
}
