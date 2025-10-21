// verifast_options{ignore_unwind_paths}
use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

unsafe fn copy_nonoverlapping(src: *const u8, dst: *mut u8, count: usize)
//@ req [?f]src[..count] |-> ?bs &*& dst[..count] |-> _;
//@ ens [f]src[..count] |-> bs &*& dst[..count] |-> bs;
{
    let mut i = 0;
    loop {
        /*@
        req [?f1]src[i..count] |-> ?bs1 &*& dst[i..count] |-> _;
        ens [f1]src[old_i..count] |-> bs1 &*& dst[old_i..count] |-> bs1;
        @*/
        //@ open array(src + i, count - i, _);
        //@ open array_(dst + i, count - i, _);
        if i == count { break; }
        *dst.add(i) = *src.add(i);
        i += 1;
    }
}

fn main()
//@ req true;
//@ ens true;
{
    unsafe {
        let buffer1: [u8; _] = [10, 20, 30];
        let buffer2 = alloc(Layout::from_size_align_unchecked(3, 1));
        if buffer2.is_null() {
            handle_alloc_error(Layout::from_size_align_unchecked(3, 1));
        }
        copy_nonoverlapping(&raw const buffer1 as *const u8, buffer2, 3);
        //@ open array(buffer2, 3, _);
        std::hint::assert_unchecked(*buffer2.add(1) == 20);
        //@ close array(buffer2, 3, _);
        //@ array_to_array_(buffer2);
        dealloc(buffer2, Layout::from_size_align_unchecked(3, 1));
        //@ array_to_array_(&buffer1 as *u8);
    }
}
