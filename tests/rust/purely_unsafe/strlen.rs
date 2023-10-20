unsafe fn assert(_b: bool)
//@ requires _b;
//@ ensures true;
{}

/*@

predicate zstr(unsigned __int8 *p; list<unsigned __int8> cs) =
    *p |-> ?c &*&
    c == 0 ?
        cs == {}
    :
        zstr(p + 1, ?cs0) &*&
        cs == cons(c, cs0);

@*/

unsafe fn strlen(mut p: *const u8) -> i32
//@ requires [?f]zstr(p, ?cs);
//@ ensures [f]zstr(p, cs) &*& result == length(cs);
{
    //@ open zstr(p, cs);
    if *p == 0 {
        //@ close [f]zstr(p, cs);
        return 0;
    } else {
        //@ open zstr(p + 1, ?cs1);
        //@ integer__limits(p + 1);
        //@ close [f]zstr(p + 1, cs1);
        //@ assume(length(cs1) < 0x7fffffff);
        return 1 + strlen(p.offset(1));
    }
}

fn main() {
    unsafe {
        let layout = std::alloc::Layout::from_size_align_unchecked(4, 1);
        let p = std::alloc::alloc(layout);
        if p.is_null() {
            std::alloc::handle_alloc_error(layout);
        }
        *p = 'H' as u8;
        *p.offset(1) = 'i' as u8;
        *p.offset(2) = '!' as u8;
        *p.offset(3) = 0;
        //@ close zstr(p + 3, "");
        //@ close zstr(p + 2, "!");
        //@ close zstr(p + 1, "i!");
        //@ close zstr(p, "Hi!");

        let n = strlen(p);
        assert(n == 3);
        //@ open zstr(p, _);
        //@ open zstr(p + 1, _);
        //@ open zstr(p + 2, _);
        //@ open zstr(p + 3, _);
        //@ close integers_(p + 3, 1, false, 1, _);
        //@ close integers_(p + 2, 1, false, 2, _);
        //@ close integers_(p + 1, 1, false, 3, _);
        //@ close integers_(p, 1, false, 4, _);

        std::alloc::dealloc(p, layout);
    }
}
