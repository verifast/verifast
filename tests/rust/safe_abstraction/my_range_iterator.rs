//@ use std::option::Option;

struct MyStruct<T> {
    x: Option<T>
}

/*@

lem MyStruct_drop<T>()
    req MyStruct_own::<T>(?_t, ?_v);
    ens <std::option::Option<T>>.own(_t, _v.x);
{
    assume(false);
}

lem MyStruct_own_mono<T0, T1>()
    req type_interp::<T0>() &*& type_interp::<T1>() &*& MyStruct_own::<T0>(?t, ?v) &*& is_subtype_of::<T0, T1>() == true;
    ens type_interp::<T0>() &*& type_interp::<T1>() &*& MyStruct_own::<T1>(t, MyStruct::<T1> { x: upcast(v.x) });
{
    assume(false);
}

lem MyStruct_send<T>(t1: thread_id_t)
    req type_interp::<T>() &*& is_Send(typeid(T)) == true &*& MyStruct_own::<T>(?t0, ?v);
    ens type_interp::<T>() &*& MyStruct_own::<T>(t1, v);
{
    assume(false);
}

@*/

//@ pred<T> <MyStruct<T>>.own(t, v) = <Option<T>>.own(t, v.x);

impl<U> Iterator for MyStruct<U> {
    type Item = U;

    fn next(self: &mut MyStruct<U>) -> Option<U> // forall U, Iterator::next::<MyStruct<U>>
    //@ req thread_token(?t) &*& *self |-> ?self0 &*& <MyStruct<U>>.own(t, self0);
    //@ ens thread_token(t) &*& *self |-> ?self1 &*& <MyStruct<U>>.own(t, self1) &*& result == self0.x &*& <Option<U>>.own(t, result);
    //@ on_unwind_ens false;
    {
        //@ open <MyStruct<U>>.own(t, self0);
        //@ open_points_to(self);
        let r = std::mem::replace(&mut self.x, None);
        //@ close_points_to(self);
        //@ close <std::option::Option<U>>.own(t, Option::None);
        //@ close <MyStruct<U>>.own(t, *self);
        r
    }
}

fn main() {
    let mut s = MyStruct { x: Some(42) };
    //@ close i32_own(_t, 42);
    //@ close <std::option::Option<i32>>.own(_t, s.x);
    //@ close <MyStruct<i32>>.own(_t, s);
    let e1 = s.next(); // Iterator::next::<MyStruct<i32>>
    //@ leak <MyStruct<i32>>.own(_t, _);
    match e1 {
        None => { unsafe { std::hint::unreachable_unchecked(); } }
        Some(x) => { unsafe { std::hint::assert_unchecked(x == 42); } }
    }
    //@ leak <Option<i32>>.own(_t, e1);
}
