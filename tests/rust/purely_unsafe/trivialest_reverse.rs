/*@

pred Nodes(n: *mut u8) =
    if n == 0 {
        true
    } else {
        *(n as *mut *mut u8) |-> ?next &*& Nodes(next)
    };

@*/

unsafe fn reverse_iter(n: *mut u8, m: *mut u8) -> *mut u8
//@ req Nodes(n) &*& Nodes(m);
//@ ens Nodes(result);
//@ on_unwind_ens false;
{
    //@ open Nodes(n);
    if n.is_null() {
        return m;
    }
    let k = *(n as *mut *mut u8);
    *(n as *mut *mut u8) = m;
    //@ close Nodes(n);
    reverse_iter(k, n)
}

unsafe fn reverse(mut n: *mut u8) -> *mut u8
//@ req Nodes(n);
//@ ens Nodes(result);
//@ on_unwind_ens false;
{
    //@ close Nodes(0);
    reverse_iter(n, std::ptr::null_mut())
}

fn main()
//@ req true;
//@ ens true;
{
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
