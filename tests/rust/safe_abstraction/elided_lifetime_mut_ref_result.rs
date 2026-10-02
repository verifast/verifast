pub struct Pair {
    pub a: u8,
    pub b: u8,
}

impl Pair {

    // By the lifetime elision rules, the result borrows `*self` for the lifetime of `self`. So the generated contract
    // must take `self` as a full borrow at that lifetime and return a full borrow of the result at the same lifetime;
    // `self` must not be treated as an in-out parameter.
    pub fn b_mut(&mut self) -> &mut u8 {
        //@ assert full_borrow(?k, Pair_full_borrow_content(_t, self)) &*& [?q]lifetime_token(k);
        //@ open_full_borrow_strong_(k, Pair_full_borrow_content(_t, self));
        //@ open Pair_full_borrow_content(_t, self)();
        //@ open Pair_own(_t, _);
        //@ open_points_to(self);
        let r = &mut self.b;
        /*@
        {
            pred Ctx() = (*self).a |-> ?a &*& struct_Pair_padding(self);
            close Ctx();
            close u8_full_borrow_content(_t, r)();
            produce_lem_ptr_chunk restore_full_borrow_(Ctx, u8_full_borrow_content(_t, r), Pair_full_borrow_content(_t, self))() {
                open Ctx();
                open u8_full_borrow_content(_t, r)();
                close_points_to(self);
                assert *self |-> ?pair1;
                close Pair_own(_t, pair1);
                close Pair_full_borrow_content(_t, self)();
            } {
                close_full_borrow_strong_();
            }
        }
        @*/
        r
    }

}

unsafe fn write_u8<'b>(r: &'b mut u8, x: u8)
//@ req thread_token(?t) &*& [?q]lifetime_token('b) &*& full_borrow('b, <u8>.full_borrow_content(t, r));
//@ ens thread_token(t) &*& [q]lifetime_token('b);
{
    //@ open_full_borrow(q, 'b, <u8>.full_borrow_content(t, r));
    //@ open u8_full_borrow_content(t, r)();
    *r = x;
    //@ close u8_full_borrow_content(t, r)();
    //@ close_full_borrow(<u8>.full_borrow_content(t, r));
    //@ leak full_borrow('b, <u8>.full_borrow_content(t, r));
}

// The caller lends `*p` at a lifetime 'a, gets a full borrow of the `b` field at 'a, and gets `*p` back when 'a ends.
unsafe fn set_b(p: *mut Pair, x: u8)
//@ req thread_token(?t) &*& t == currentThread &*& *p |-> ?pair0;
//@ ens thread_token(t) &*& *p |-> ?pair1;
{
    //@ let k = begin_lifetime();
    //@ close Pair_own(t, pair0);
    //@ close Pair_full_borrow_content(t, p)();
    //@ borrow(k, Pair_full_borrow_content(t, p));
    {
        //@ let_lft 'a = k;
        let r = Pair::b_mut/*@::<'a>@*/(&mut *p);
        write_u8/*@::<'a>@*/(r, x);
    }
    //@ end_lifetime(k);
    //@ borrow_end(k, Pair_full_borrow_content(t, p));
    //@ open Pair_full_borrow_content(t, p)();
    //@ open Pair_own(t, _);
}

// A caller that passes `*p` itself and expects it back right after the call, while the result still borrows
// `(*p).b`, must be rejected.
unsafe fn set_b_in_out(p: *mut Pair, x: u8) -> u8
//@ req thread_token(?t) &*& t == currentThread &*& *p |-> ?pair0;
//@ ens thread_token(t) &*& *p |-> ?pair1;
{
    //@ let k = begin_lifetime();
    let b;
    {
        //@ let_lft 'a = k;
        //@ close Pair_own(t, pair0);
        let r = Pair::b_mut/*@::<'a>@*/(&mut *p); //~should_fail
        //@ open Pair_own(t, _);
        b = (*p).b;
        write_u8/*@::<'a>@*/(r, x);
    }
    //@ end_lifetime(k);
    b
}

fn main() {
    let mut pair = Pair { a: 1, b: 2 };
    unsafe { set_b(&raw mut pair, 3); }
}
