unsafe fn assert(_b: bool)
//@ req _b;
//@ ens true;
{}

/*@

pred zstr(p: *u8; cs: list<u8>) =
    *p |-> ?c &*&
    if c == 0 {
        cs == []
    } else {
        zstr(p + 1, ?cs0) &*&
        cs == cons(c, cs0)
    };

fix neq<t>(x: t, y: t) -> bool { x != y }

lem u8s_zstr_join(p: *u8)
    req [?f]integers_(p, 1, false, ?n, ?cs0) &*& [f]zstr(p + n, ?cs1) &*& forall(cs0, (neq)(0)) == true;
    ens [f]zstr(p, append(cs0, cs1));
{
    open integers_(p, 1, false, n, cs0);
    if n == 0 {
    } else {
        u8s_zstr_join(p + 1);
    }
}

@*/

unsafe fn strlen_rec(mut p: *const u8) -> i32
//@ req [?f]zstr(p, ?cs);
//@ ens [f]zstr(p, cs) &*& result == length(cs);
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
        return 1 + strlen_rec(p.offset(1));
    }
}

unsafe fn strlen_inv(mut p: *const u8) -> isize
//@ req [?f]zstr(p, ?cs);
//@ ens [f]zstr(p, cs) &*& result == length(cs);
{
    let mut p1 = p;
    //@ assume(length(cs) <= isize::MAX);
    loop {
        /*@
        inv
            [f]p[..(p1 as usize - p as usize)] |-> ?cs0 &*& forall(cs0, (neq)(0)) == true &*&
            [f]zstr(p1, ?cs1) &*& cs == append(cs0, cs1) &*&
            (p1 as pointer).provenance == (p as pointer).provenance;
        @*/
        //@ open zstr(p1, cs1);
        if *p1 == 0 {
            //@ close [f]zstr(p1, cs1);
            break;
        } else {
            //@ open zstr(p1 + 1, ?cs11);
            //@ integer__limits(p1 + 1);
            //@ close [f]zstr(p1 + 1, cs11);
            //@ close [f]integers_(p1 + 1, 1, false, 0, []);
            //@ close [f]integers_(p1, 1, false, 1, _);
            //@ integers__join(p);
            //@ forall_append(cs0, [head(cs1)], (neq)(0));
            //@ append_assoc(cs0, [head(cs1)], tail(cs1));
            p1 = p1.offset(1);
        }
    }
    //@ div_rem_nonneg(p1 as usize - p as usize, 1);
    //@ u8s_zstr_join(p);
    p1.offset_from(p)
}

unsafe fn strlen(mut p: *const u8) -> isize
//@ req [?f]zstr(p, ?cs);
//@ ens [f]zstr(p, cs) &*& result == length(cs);
{
    let mut p1 = p;
    //@ assume(length(cs) <= isize::MAX);
    loop {
        /*@
        req [f]zstr(p1, ?cs1) &*& (p1 as pointer).provenance == (p as pointer).provenance;
        ens [f]zstr(old_p1, cs1) &*& p1 == old_p1 + length(cs1);
        @*/
        
        //@ open zstr(p1, cs1);
        let done = *p1 == 0;
        /*@
        if done {
            close [f]zstr(p1, cs1);
        }
        @*/
        if done {
            // FIXME: Currently, ghost commands on exit paths are executed *after checking the loop's postcondition* :-(
            // As a workaround, duplicate the conditional in ghost code.
            break;
        } else {
            //@ open zstr(p1 + 1, ?cs11);
            //@ integer__limits(p1 + 1);
            //@ close [f]zstr(p1 + 1, cs11);
            p1 = p1.offset(1);
        }
    }
    //@ div_rem_nonneg(p1 as usize - p as usize, 1);
    p1.offset_from(p)
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
