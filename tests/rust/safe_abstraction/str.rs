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
