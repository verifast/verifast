/*@

pred llist(head: *mut u8) =
    if head == 0 {
        true
    } else {
        *(head as *mut *mut u8) |-> ?next &*& llist(next)
    };

@*/

unsafe fn reverse_iter(original: *mut u8, reversed: *mut u8) -> *mut u8
//@ req llist(original) &*& llist(reversed);
//@ ens llist(result);
//@ on_unwind_ens false;
{
    //@ open llist(original);
    if original.is_null() {
        return reversed;
    }
    let next = *(original as *mut *mut u8);
    *(original as *mut *mut u8) = reversed;
    //@ close llist(original);
    reverse_iter(next, original)
}

unsafe fn reverse(mut list: *mut u8) -> *mut u8
//@ req llist(list);
//@ ens llist(result);
//@ on_unwind_ens false;
{
    //@ close llist(0);
    reverse_iter(list, std::ptr::null_mut())
}

fn main()
//@ req true;
//@ ens true;
{
    unsafe {
        //@ close llist(0);
        let mut node1: *mut u8 = std::ptr::null_mut();
        //@ close llist(&node1 as *mut u8);
        let mut node2 = &raw mut node1 as *mut u8;
        //@ close llist(&node2 as *mut u8);
        let mut node3 = &raw mut node2 as *mut u8;
        //@ close llist(&node3 as *mut u8);
        let reversed = reverse(&raw mut node3 as *mut u8);
        reverse(reversed);
        std::process::abort();
    }
}
