pub struct Pair<A, B> {
    pub x: A,
    pub y: B,
}

pub fn bad_own<A, B>(pair: Pair<A, B>) { //~allow_dead_code
    unsafe { std::hint::unreachable_unchecked(); } //~should_fail
} //~allow_dead_code

pub fn bad_share<'a, A, B>(pair: &'a Pair<A, B>) { //~allow_dead_code
    //@ open <Pair<A, B>>.share('a, _t, pair);
    unsafe { std::hint::unreachable_unchecked(); } //~should_fail
}


pub fn drop<A, B>(pair: Pair<A, B>) {}

pub fn get_x<'a, A, B>(pair: &'a Pair<A, B>) -> &'a A {
    //@ open <Pair<A, B>>.share('a, _t, pair);
    //@ let p = precreate_ref(&(*pair).x);
    //@ produce_type_interp::<A>();
    //@ init_ref_share::<A>('a, _t, p);
    //@ leak type_interp::<A>();
    //@ open_frac_borrow('a, ref_initialized_::<A>(p), _q_a);
    //@ open [?f]ref_initialized_::<A>(p)();
    let r = &pair.x;
    //@ close [f]ref_initialized_::<A>(p)();
    //@ close_frac_borrow(f, ref_initialized_::<A>(p));
    r
}
