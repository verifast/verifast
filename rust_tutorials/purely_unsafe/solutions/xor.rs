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
    //@ open bytes_(start, count);
    if count > 0 {
        let b = read_byte();
        *start = b;
        read_bytes(start.add(1), count - 1);
    }
    //@ close bytes(start, count);
}

unsafe fn xor_bytes(text: *mut u8, key: *mut u8, count: usize)
//@ req bytes(text, count) &*& bytes(key, count);
//@ ens bytes(text, count) &*& bytes(key, count);
{
    if count > 0 {
        //@ open bytes(text, count);
        //@ open bytes(key, count);
        let t = *text;
        let k = *key;
        *text = t ^ k;
        xor_bytes(text.add(1), key.add(1), count - 1);
        //@ close bytes(text, count);
        //@ close bytes(key, count);
    }
}

unsafe fn write_bytes(start: *mut u8, count: usize)
//@ req bytes(start, count);
//@ ens bytes(start, count);
{
    if count > 0 {
        //@ open bytes(start, count);
        let b = *start;
        write_byte(b);
        write_bytes(start.add(1), count - 1);
        //@ close bytes(start, count);
    }
}

fn main()
//@ req true;
//@ ens true;
{
    unsafe {
        let text = alloc(10);
        let key = alloc(10);
        read_bytes(text, 10);
        read_bytes(key, 10);
        xor_bytes(text, key, 10);
        write_bytes(text, 10);
        //@ leak bytes(text, 10) &*& bytes(key, 10);
    }
}
