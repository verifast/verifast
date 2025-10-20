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

/*@

lem_auto bytes_count_nonneg()
    req bytes(?start, ?count);
    ens bytes(start, count) &*& 0 <= count;
{
    open bytes(start, count);
    if count != 0 {
        bytes_count_nonneg();
    }
    close bytes(start, count);
}

lem bytes_add_byte(start: *mut u8)
    req bytes(start, ?count) &*& *(start + count) |-> ?_;
    ens bytes(start, count + 1);
{
    open bytes(start, count);
    if count == 0 {
        close bytes(start + 1, 0);
    } else {
        bytes_add_byte(start + 1);
    }
    close bytes(start, count + 1);
}

@*/

unsafe fn read_bytes(start: *mut u8, count: usize)
//@ req bytes_(start, count);
//@ ens bytes(start, count);
{
    //@ close bytes(start, 0);
    let mut i = 0;
    loop {
        //@ inv bytes(start, i) &*& bytes_(start + i, count - i);
        if i == count { break; }
        let b = read_byte();
        //@ open bytes_(start + i, count - i);
        *start.add(i) = b;
        //@ bytes_add_byte(start);
        i += 1;
    }
    //@ open bytes_(start + count, 0);
}

unsafe fn write_bytes(start: *mut u8, count: usize)
//@ req bytes(start, count);
//@ ens bytes(start, count);
{
    //@ close bytes(start, 0);
    let mut i = 0;
    loop {
        //@ inv bytes(start, i) &*& bytes(start + i, count - i);
        if i == count { break; }
        //@ open bytes(start + i, count - i);
        let b = *start.add(i);
        //@ bytes_add_byte(start);
        write_byte(b);
        i += 1;
    }
    //@ open bytes(start + count, 0);
}

fn main()
//@ req true;
//@ ens true;
{
    unsafe {
        let array = alloc(100);
        read_bytes(array, 100);
        write_bytes(array, 100);
        write_bytes(array, 100);
        //@ leak bytes(array, 100);
    }
}
