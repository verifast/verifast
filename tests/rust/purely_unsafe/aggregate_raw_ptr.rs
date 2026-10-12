#![feature(core_intrinsics)]
#![allow(internal_features)]

// `core::intrinsics::aggregate_raw_ptr` builds a raw pointer from a thin pointer and pointer metadata. In MIR, a call
// of it becomes an `AggregateKind::RawPtr` aggregate. `Vec::as_slice` and `Vec::as_mut_slice` use it to build a slice
// pointer from the buffer pointer and the length.

use std::intrinsics::aggregate_raw_ptr;

unsafe fn slice_ptr<T>(data: *const T, len: usize) -> *const [T]
//@ req true;
//@ ens result as *T == data &*& result.len() == len;
{
    aggregate_raw_ptr::<*const [T], _, _>(data, len)
}

unsafe fn slice_ptr_mut(data: *mut u8, len: usize) -> *mut [u8]
//@ req true;
//@ ens result as *u8 == data &*& result.len() == len;
{
    aggregate_raw_ptr::<*mut [u8], _, _>(data, len)
}

// The data pointer need not point to the element type.
unsafe fn slice_ptr_from_bytes(data: *const u8, len: usize) -> *const [u16]
//@ req true;
//@ ens result as *u16 == data as *u16 &*& result.len() == len;
{
    aggregate_raw_ptr::<*const [u16], _, _>(data, len)
}

// Element types that mention a lifetime.
unsafe fn slice_ptr_of_refs<'a>(data: *const &'a u8, len: usize) -> *const [&'a u8]
//@ req true;
//@ ens result as *&'a u8 == data &*& result.len() == len;
{
    aggregate_raw_ptr::<*const [&'a u8], _, _>(data, len)
}

// As in `Vec::as_slice` and `Vec::as_mut_slice`.
unsafe fn as_slice<'a>(data: *const u8, len: usize) -> &'a [u8]
//@ req [?f]data[..len] |-> ?vs;
//@ ens [f]data[..len] |-> vs &*& result as *u8 == data &*& result.len() == len;
{
    &*aggregate_raw_ptr::<*const [u8], _, _>(data, len)
}

unsafe fn as_mut_slice<'a, T>(data: *mut T, len: usize) -> &'a mut [T]
//@ req data[..len] |-> ?vs;
//@ ens data[..len] |-> vs &*& result as *T == data &*& result.len() == len;
{
    &mut *aggregate_raw_ptr::<*mut [T], _, _>(data, len)
}

unsafe fn first(data: *const i32, len: usize) -> i32
//@ req [?f]data[..len] |-> ?vs &*& 0 < len;
//@ ens [f]data[..len] |-> vs &*& result == head(vs);
{
    let s = aggregate_raw_ptr::<*const [i32], _, _>(data, len);
    *(s as *const i32)
}

unsafe fn wrong_len<T>(data: *const T, len: usize) -> *const [T]
//@ req true;
//@ ens result.len() == 0; //~should_fail
{
    aggregate_raw_ptr::<*const [T], _, _>(data, len)
}

fn main() {}
