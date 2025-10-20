// verifast_options{ignore_unwind_paths disable_overflow_check}
use std::io::{Read, Write, stdin, stdout};

unsafe fn read_byte() -> u8
//@ req true;
//@ ens true;
//@ assume_correct
{
    let mut buf = [0u8];
    stdin().read_exact(&mut buf[..]).unwrap();
    buf[0]
}

unsafe fn write_byte(value: u8)
//@ req true;
//@ ens true;
//@ assume_correct
{
    let buf = [value];
    stdout().write(&buf[..]).unwrap();
}

/*@

pred bytes_(start: *mut u8, count: usize) =
    if count == 0 { true } else { *start |-> _ &*& bytes_(start + 1, count - 1) };

pred bytes(start: *mut u8, count: usize) =
    if count == 0 { true } else { *start |-> ?_ &*& bytes(start + 1, count - 1) };

@*/

unsafe fn alloc(count: usize) -> *mut u8
//@ req 1 <= count;
//@ ens bytes_(result, count);
//@ assume_correct
{
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    result
}

unsafe fn read_bytes(start: *mut u8, count: usize)
//@ req bytes_(start, count);
//@ ens bytes(start, count);
{
    let mut i = 0;
    loop {
        /*@
        req bytes_(start + i, count - i);
        ens bytes(start + old_i, count - old_i);
        @*/
        //@ open bytes_(start + i, count - i);
        //@ if i == count { close bytes(start + i, 0); }
        if i == count { break; }
        let b = read_byte();
        *start.add(i) = b;
        i += 1;
        //@ recursive_call();
        //@ close bytes(start + old_i, count - old_i);
    }
}

unsafe fn write_bytes(start: *mut u8, count: usize)
//@ req bytes(start, count);
//@ ens bytes(start, count);
{
    let mut i = 0;
    loop {
        /*@
        req bytes(start + i, count - i);
        ens bytes(start + old_i, count - old_i);
        @*/
        if i == count { break; }
        //@ open bytes(start + i, count - i);
        write_byte(*start.add(i));
        i += 1;
        //@ recursive_call();
        //@ close bytes(start + old_i, count - old_i);
    }
}

fn main() {
    unsafe {
        let array = alloc(100);
        read_bytes(array, 100);
        write_bytes(array, 100);
        write_bytes(array, 100);
        //@ leak bytes(array, 100);
    }
}
