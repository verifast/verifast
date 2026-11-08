// verifast_options{skip_specless_fns}

// Soundness tests for local lifetimes, stack permissions, leak checking, and drop semantics.

pub struct SimpleBox {
    pub val: i32,
    pub tag: u8,
}

pub struct DropTracker {
    ptr: *mut i32,
}

/*@
pred <DropTracker>.own(t, tracker) = true;
@*/

impl DropTracker {
    pub fn new() -> DropTracker {
        let r = DropTracker { ptr: std::ptr::null_mut() };
        //@ close DropTracker_own(_t, r);
        r
    }
}

// =========================================================================
// POSITIVE CASES
// =========================================================================

// Taking address of local variable, writing through it, and observing updated value
pub fn test_valid_stack_address() -> i32 {
    let mut x = 10;
    let p = &raw mut x;
    unsafe {
        *p = 25;
    }
    x
}

// Struct mutation with accurate postcondition
pub unsafe fn test_valid_struct_mut(b: *mut SimpleBox)
//@ req (*b).val |-> ?v0 &*& (*b).tag |-> ?t0;
//@ ens (*b).val |-> 42 &*& (*b).tag |-> t0;
{
    (*b).val = 42;
}

// Block scope drop without leaks
pub fn test_valid_block_scope() -> i32 {
    let x = 5;
    {
        let _y = x + 10;
    }
    x
}

// Dropping a type with an .own predicate without consuming it leaks the own chunk
pub fn neg_drop_unconsumed_own() {
    let _tracker = DropTracker::new();
} //~should_fail

// =========================================================================
// NEGATIVE CASES: 10 should_fail cases
// =========================================================================

// 1. Returning a raw pointer to a local stack variable and dereferencing it in caller
fn return_dangling_local() -> *mut i32
//@ req true;
//@ ens true;
{
    let mut x = 42;
    &raw mut x
}

pub unsafe fn neg_deref_dangling_local() -> i32
//@ req true;
//@ ens true;
{
    let p = return_dangling_local();
    *p //~should_fail
} //~allow_dead_code

// 2. Leaking a heap allocation on function return (leak check failure)
pub unsafe fn neg_leak_heap_alloc()
//@ req true;
//@ ens true;
{
    let layout = std::alloc::Layout::new::<u8>();
    let p = std::alloc::alloc(layout);
    if p.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
} //~should_fail

// 3. Leaking a points-to chunk on function return (leak check failure)
pub unsafe fn neg_leak_points_to(p: *mut i32)
//@ req *p |-> 42;
//@ ens true;
{
} //~should_fail

// 4. Invalid postcondition after struct mutation (claiming unmodified value)
pub unsafe fn neg_struct_mut_false_post(b: *mut SimpleBox)
//@ req (*b).val |-> ?v0;
//@ ens (*b).val |-> v0; //~should_fail
{
    (*b).val = 99;
}

// 5. Invalid postcondition claiming other unmutated field was changed
pub unsafe fn neg_struct_other_field_false_post(b: *mut SimpleBox)
//@ req (*b).val |-> ?v0 &*& (*b).tag |-> 1;
//@ ens (*b).val |-> 42 &*& (*b).tag |-> 2; //~should_fail
{
    (*b).val = 42;
}

// Helper to mutate via raw const pointer
unsafe fn mutate_raw_const(p: *const i32)
//@ req *p |-> _;
//@ ens *p |-> 42;
{
    *(p as *mut i32) = 42;
}

// 6. Mutating an immutable stack local via raw pointer (UB detected by VeriFast)
pub fn neg_mutate_immut_local()
//@ req true;
//@ ens true;
{
    let x = 24;
    unsafe { mutate_raw_const(&raw const x); } //~should_fail
} //~allow_dead_code

// 7. Modifying a place through raw pointer after points-to was consumed
pub unsafe fn neg_write_after_consumed(p: *mut i32)
//@ req *p |-> 10;
//@ ens true;
{
    let q = p;
    //@ leak *p |-> 10;
    *q = 20; //~should_fail
} //~allow_dead_code

// 8. False postcondition on local variable return
pub fn neg_false_local_post() -> i32
//@ req true;
//@ ens result == 100; //~should_fail
{
    42
}

// 9. Leaking fractional points-to permission [1/2] on return
pub unsafe fn neg_leak_fractional(p: *mut i32)
//@ req [1/2](*p) |-> ?v;
//@ ens true;
{
} //~should_fail

// 10. Consuming struct field twice without permission
pub unsafe fn neg_double_consume_field(b: *mut SimpleBox)
//@ req (*b).val |-> 1;
//@ ens (*b).val |-> 1 &*& (*b).tag |-> 2; //~should_fail
{
}

fn main() {}
