// verifast_options{skip_specless_fns}

// Soundness tests for raw slice fat pointers (*const [T] and *mut [T]).
// A raw slice pointer value owns nothing, and a place holding one is
// described by a points-to chunk. Converting to references or reading
// memory requires explicit permissions.

pub struct SliceStore<T> {
    pub const_slice: *const [T],
    pub mut_slice: *mut [T],
    pub count: usize,
}

pub struct SlicePair<T, U> {
    pub a: *mut [T],
    pub b: *const [U],
}

// =========================================================================
// POSITIVE CASES
// =========================================================================

// Storing and loading *const [i32] and *mut [u64] in structs
pub unsafe fn store_and_load_const(s: *mut SliceStore<i32>, new_c: *const [i32]) -> *const [i32]
//@ req (*s).const_slice |-> ?old_c;
//@ ens (*s).const_slice |-> new_c &*& result == old_c;
{
    let old = (*s).const_slice;
    (*s).const_slice = new_c;
    old
}

pub unsafe fn store_and_load_mut(s: *mut SliceStore<u64>, new_m: *mut [u64]) -> *mut [u64]
//@ req (*s).mut_slice |-> ?old_m;
//@ ens (*s).mut_slice |-> new_m &*& result == old_m;
{
    let old = (*s).mut_slice;
    (*s).mut_slice = new_m;
    old
}

// Passing raw slice pointers through helper functions
pub fn pass_const_slice<T>(p: *const [T]) -> *const [T] {
    p
}

pub fn pass_mut_slice<T>(p: *mut [T]) -> *mut [T] {
    p
}

// Storing in a local variable and returning
pub fn local_slice_var<T>(p: *mut [T]) -> *mut [T] {
    let q = p;
    q
}

// Tuples containing raw slice pointers
pub unsafe fn slice_pair<T, U>(p: *mut [T], q: *const [U]) -> SlicePair<T, U>
//@ req true;
//@ ens result.a == p &*& result.b == q;
{
    SlicePair { a: p, b: q }
}

// Borrowing &*const [T] and &mut *mut [T]
pub fn borrow_const_slice<'a, T>(_r: &'a *const [T]) {}

pub fn borrow_and_set_mut_slice<T>(r: &mut *mut [T], new_p: *mut [T]) {
    *r = new_p;
}

// =========================================================================
// NEGATIVE CASES: 10 should_fail cases
// =========================================================================

// 1. Reading a fat pointer *mut [u8] through a thin pointer *mut u8 without proper layout
unsafe fn neg_read_fat_as_thin<T>(s: *mut *mut [T]) -> *mut u8
//@ req *s |-> ?v;
//@ ens true;
{
    *(s as *mut *mut u8) //~should_fail
} //~allow_dead_code

// 2. Converting *mut [u8] to &mut [u8] without points-to / slice permission
pub fn neg_forge_mut_ref<'a>(p: *mut [u8]) -> &'a mut [u8] { //~should_fail
    unsafe { &mut *p }
}

// 3. Converting *const [u8] to &[u8] without points-to / slice permission
pub fn neg_forge_shared_ref<'a>(p: *const [u8]) -> &'a [u8] { //~should_fail
    unsafe { &*p }
}

// 4. Reading struct's const_slice field without permission
unsafe fn neg_read_field_without_perm(s: *mut SliceStore<i32>) -> *const [i32]
//@ req true;
//@ ens true;
{
    (*s).const_slice //~should_fail
} //~allow_dead_code

// 5. Writing struct's mut_slice field without permission
unsafe fn neg_write_field_without_perm(s: *mut SliceStore<u64>, p: *mut [u64])
//@ req true;
//@ ens true;
{
    (*s).mut_slice = p; //~should_fail
} //~allow_dead_code

// 6. Mutating struct's mut_slice field when only shared read permission ([1/2]) is held
unsafe fn neg_write_with_half_perm(s: *mut SliceStore<u64>, p: *mut [u64])
//@ req [1/2](*s).mut_slice |-> _;
//@ ens true;
{
    (*s).mut_slice = p; //~should_fail
} //~allow_dead_code

// 7. Claiming two disjoint raw slice fields are equal when they are independent
unsafe fn neg_claim_disjoint_equal(s: *mut SliceStore<u8>)
//@ req (*s).const_slice |-> ?c &*& (*s).mut_slice |-> ?m;
//@ ens (*s).const_slice |-> c &*& (*s).mut_slice |-> m &*& c == m as *const [u8]; //~should_fail
{
}

// 8. False postcondition claiming returned pointer equals null slice when arbitrary
pub fn neg_false_return_val(p: *mut [i32], q: *mut [i32]) -> *mut [i32]
//@ req true;
//@ ens result == q; //~should_fail
{
    p
}

// 9. Consuming struct field permission twice (aliasing violation)
unsafe fn neg_consume_twice(s: *mut SliceStore<i32>)
//@ req (*s).const_slice |-> ?c;
//@ ens (*s).const_slice |-> c &*& (*s).mut_slice |-> _; //~should_fail
{
}

// 10. Reading from pair struct without permission on field b
unsafe fn neg_read_pair_unheld(p: *mut SlicePair<u8, u16>) -> *const [u16]
//@ req (*p).a |-> ?_a;
//@ ens true;
{
    (*p).b //~should_fail
} //~allow_dead_code

fn main() {}
