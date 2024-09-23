pub struct Foo {
    field1: i32,
    field2: u8
}

/*@

pred <Foo>.own(t, foo) = true;

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

pred <Bar>.own(t, bar) = true;

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
