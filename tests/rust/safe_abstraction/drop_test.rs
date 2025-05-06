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
        //@ open Foo_own(_, _);
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
        let r = Bar { fd: std::ptr::null_mut() };
        //@ close Bar_own(_t, r);
        r
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
