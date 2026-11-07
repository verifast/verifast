// A struct with a raw slice pointer field (`*mut [T]`), as in `core::slice::ChunksMut`.
// Like a thin raw pointer, a `*const/mut [T]` value owns nothing, and a place holding one is
// described by a plain points-to chunk.

pub struct RawSlice<T> {
    v: *mut [T],
    n: usize,
}

unsafe fn replace_v<T>(s: *mut RawSlice<T>, w: *mut [T]) -> *mut [T]
//@ req (*s).v |-> ?v0;
//@ ens (*s).v |-> w &*& result == v0;
{
    let old = (*s).v;
    (*s).v = w;
    old
}

// Semantic well-typedness of a safe function that takes and returns a raw slice pointer.
pub fn id_raw_slice<T>(p: *mut [T]) -> *mut [T] {
    p
}

// A stored fat pointer cannot be read back as a thin pointer (its layout is unspecified).
unsafe fn read_as_thin<T>(s: *mut *mut [T]) -> *mut u8
//@ req *s |-> ?v;
//@ ens *s |-> v &*& result == v as *u8;
{
    *(s as *mut *mut u8) //~should_fail
} //~allow_dead_code

// Owning a raw slice pointer gives no access to the memory it points to.
pub fn forge<'a>(p: *mut [u8]) -> &'a mut [u8] { //~should_fail
    unsafe { &mut *p }
}


// Full borrow content of a place holding a raw slice pointer: write through `&mut`.
pub fn set_through_mut_ref(r: &mut *mut [u8], p: *mut [u8]) {
    *r = p;
}

// Shared ownership of a place holding a raw slice pointer.
pub fn take_shared_ref(_r: &*mut [u8]) {}

fn main() {}
