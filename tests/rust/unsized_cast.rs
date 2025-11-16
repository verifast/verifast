unsafe fn foo<T: ?Sized>(p: *const T, q: *const T) -> bool
//@ req (p as *u8) == (q as *u8);
//@ ens result; //~should_fail
{ p == q }
