unsafe fn size_of_ptr<T: ?Sized>() -> usize
//@ req true;
//@ ens result == 8; //~should_fail
{ std::mem::size_of::<*const T>() }
