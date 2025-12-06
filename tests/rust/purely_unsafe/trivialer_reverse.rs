/*@

pred Nodes(n: *mut u8) =
    if n == 0 {
        true
    } else {
        *(n as *mut *mut u8) |-> ?next &*& Nodes(next)
    };

@*/

unsafe fn reverse(mut n: *mut u8) -> *mut u8
//@ req Nodes(n);
//@ ens Nodes(result);
//@ on_unwind_ens false;
{
    let mut m = std::ptr::null_mut();
    //@ close Nodes(0);
    loop {
        //@ inv Nodes(n) &*& Nodes(m);
        //@ open Nodes(n);
        if n.is_null() {
            return m;
        }
        let k = *(n as *mut *mut u8);
        *(n as *mut *mut u8) = m;
        m = n;
        n = k;
        //@ close Nodes(m);
    }
}

fn main() {
    unsafe {
        //@ close Nodes(0);
        let mut node1: *mut u8 = std::ptr::null_mut();
        //@ close Nodes(&node1 as *mut u8);
        let mut node2: *mut u8 = &raw mut node1 as *mut u8;
        //@ close Nodes(&node2 as *mut u8);
        reverse(&raw mut node2 as *mut u8);
        std::process::abort();
    }
}
