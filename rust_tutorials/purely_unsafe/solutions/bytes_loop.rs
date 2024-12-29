// verifast_options{disable_overflow_check}

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

pred bytes(start: *mut u8, count: usize) =
    if count <= 0 { true } else { *start |-> ?_ &*& bytes(start + 1, count - 1) };

@*/

unsafe fn alloc(count: usize) -> *mut u8
//@ req 1 <= count;
//@ ens bytes(result, count);
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

lem split_bytes_chunk(start: *mut u8, i: usize)
    req bytes(start, ?count) &*& 0 <= i &*& i <= count;
    ens bytes(start, i) &*& bytes(start + i, count - i);
{
    if i == 0 {
        close bytes(start, 0);
    } else {
        open bytes(start, count);
        split_bytes_chunk(start + 1, i - 1);
        close bytes(start, i);
    }
}

lem merge_bytes_chunk(start: *mut u8)
    req bytes(start, ?i) &*& bytes(start + i, ?count) &*& 0 <= i &*& 0 <= count;
    ens bytes(start, i + count);
{
    open bytes(start, i);
    if i != 0 {
        merge_bytes_chunk(start + 1);
        close bytes(start, i + count);
    }
}

@*/

unsafe fn read_bytes(start: *mut u8, count: usize)
//@ req bytes(start, count);
//@ ens bytes(start, count);
{
    let mut i = 0;
    loop {
        //@ inv bytes(start, count) &*& 0 <= i;
        if i >= count {
            break;
        }
        let b = read_byte();
        //@ split_bytes_chunk(start, i);
        //@ open bytes(start + i, count - i);
        *start.add(i) = b;
        //@ close bytes(start + i, count - i);
        //@ merge_bytes_chunk(start);
        i += 1;
    }
}

unsafe fn write_bytes(start: *mut u8, count: usize)
//@ req bytes(start, count);
//@ ens bytes(start, count);
{
    let mut i = 0;
    loop {
        //@ inv bytes(start, count) &*& 0 <= i;
        if i >= count {
            break;
        }
        //@ split_bytes_chunk(start, i);
        //@ open bytes(start + i, count - i);
        let b = *start.add(i);
        //@ close bytes(start + i, count - i);
        //@ merge_bytes_chunk(start);
        write_byte(b);
        i += 1;
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
