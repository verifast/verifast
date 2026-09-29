fn test_str<'a>(s: &'a str) -> &'a str
//@ req [?qa]lifetime_token('a) &*& [_](<str>.share('a, currentThread, s));
//@ ens [qa]lifetime_token('a) &*& [_](<str>.share('a, currentThread, result));
//@ on_unwind_ens false;
{
    let s_ptr = s as *const str;
    if (s_ptr as *mut [u8]).len() > 0 {
        //@ open str_share('a, currentThread, s);
        //@ assert [_]exists(?bs);
        //@ open_frac_borrow('a, mk_array(s as *u8, s.len(), bs), qa);
        //@ open [?f]mk_array::<u8>(s as *u8, s.len(), bs)();
        //@ assert bs == cons(?b0, ?rest0);
        /*@
        if 0x80 <= b0 {
            assert rest0 == cons(?b1, ?rest1);
            if 0xE0 <= b0 {
                assert rest1 == cons(?b2, ?rest2);
                if 0xF0 <= b0 {
                    assert rest2 == cons(?b3, ?rest3);
                    if b0 == 0xF0 {
                        assert 0x90 <= b1;
                    }
                }
            }
        }
        @*/
        unsafe { std::hint::assert_unchecked(*(s_ptr as *const u8) <= 0x7F || 0x80 <= *(s_ptr as *const u8).add(1)); }
        //@ close [f]mk_array::<u8>(s as *u8, s.len(), bs)();
        //@ close_frac_borrow(f, mk_array(s as *u8, s.len(), bs));
    }
    s
}

/*@

lem is_valid_utf8_ed_9f()
    req true;
    ens true;
{
    // U+D7C0..U+D7FF are encoded as ED 9F 80..ED 9F BF and are valid UTF-8.
    assert is_valid_utf8(cons(0xED, cons(0x9F, cons(0xBF, nil)))) == true; // U+D7FF
    assert is_valid_utf8(cons(0xED, cons(0x9F, cons(0x80, nil)))) == true; // U+D7C0
    // ED A0 80 (U+D800) is a surrogate and must stay invalid.
    assert is_valid_utf8(cons(0xED, cons(0xA0, cons(0x80, nil)))) == false;
}

@*/
