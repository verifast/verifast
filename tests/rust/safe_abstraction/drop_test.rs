pub struct Foo {
    field1: i32,
    field2: u8
}

/*@

pred Foo_own(t: thread_id_t, foo: Foo) = true;

pred Foo_share(k: lifetime_t, t: thread_id_t, l: *Foo) = true;

lem Foo_share_mono(k: lifetime_t, k1: lifetime_t, t: thread_id_t, l: *Foo)
    req lifetime_inclusion(k1, k) == true &*& [_]Foo_share(k, t, l);
    ens [_]Foo_share(k1, t, l);
{
    close Foo_share(k1, t, l);
    leak Foo_share(k1, t, l);
}

lem Foo_share_full(k: lifetime_t, t: thread_id_t, l: *Foo)
    req full_borrow(k, Foo_full_borrow_content(t, l)) &*& [?q]lifetime_token(k);
    ens [_]Foo_share(k, t, l) &*& [q]lifetime_token(k);
{
    close Foo_share(k, t, l);
    leak Foo_share(k, t, l);
    leak full_borrow(_, _);
}

@*/

impl Drop for Foo {
    fn drop<'a>(&'a mut self) {
        //@ open Foo_full_borrow_content(_t, self)();
        //@ close i32_full_borrow_content(_t, &(*self).field1)();
        //@ close u8_full_borrow_content(_t, &(*self).field2)();
    }
}

pub struct Bar {
    fd: *mut u8
}

/*@

pred Bar_own(t: thread_id_t, bar: Bar) = true;

pred Bar_share(k: lifetime_t, t: thread_id_t, l: *Bar) = true;

lem Bar_share_mono(k: lifetime_t, k1: lifetime_t, t: thread_id_t, l: *Bar)
    req lifetime_inclusion(k1, k) == true &*& [_]Bar_share(k, t, l);
    ens [_]Bar_share(k1, t, l);
{
    close Bar_share(k1, t, l);
    leak Bar_share(k1, t, l);
}

lem Bar_share_full(k: lifetime_t, t: thread_id_t, l: *Bar)
    req full_borrow(k, Bar_full_borrow_content(t, l)) &*& [?q]lifetime_token(k);
    ens [_]Bar_share(k, t, l) &*& [q]lifetime_token(k);
{
    close Bar_share(k, t, l);
    leak Bar_share(k, t, l);
    leak full_borrow(_, _);
}

@*/

impl Bar {
    pub fn new() -> Bar {
        Bar { fd: std::ptr::null_mut() }
    }
}

impl Drop for Bar {
    fn drop<'a>(&'a mut self)
    //@ req false; //~ should_fail
    //@ ens true;
    {
        unsafe {
            *self.fd = 42;
        }
    }
}
