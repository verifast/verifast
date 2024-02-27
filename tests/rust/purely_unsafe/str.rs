unsafe fn is_hi<'a>(text: &'a str) -> bool
//@ req [?f]integers_(text.ptr, 1, false, text.len, ?cs);
//@ ens [f]integers_(text.ptr, 1, false, text.len, cs) &*& result == (cs == ['H', 'i']);
{
    if text.len() != 2 {
        false
    } else {
        //@ open integers_(_, _, _, _, _);
        //@ open integers_(_, _, _, _, _);
        //@ open integers_(_, _, _, _, _);
        *text.as_ptr() == b'H' && *text.as_ptr().offset(1) == b'i'
    }
}

unsafe fn assert(_b: bool)
//@ req _b;
//@ ens true;
{}

unsafe fn test_is_hi()
//@ req true;
//@ ens true;
{
    assert(is_hi("Hi"));
    assert(!is_hi("Lo"));
    assert(!is_hi("Hi!"));
}
