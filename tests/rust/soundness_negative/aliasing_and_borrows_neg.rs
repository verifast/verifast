// verifast_options{skip_specless_fns}

// Soundness tests for pointer aliasing, permissions, and heap ownership.

// =========================================================================
// POSITIVE CASES
// =========================================================================

// Valid allocation, initialization, read, and deallocation
unsafe fn test_valid_alloc_lifecycle()
//@ req true;
//@ ens true;
{
    let layout = std::alloc::Layout::new::<i32>();
    let p = std::alloc::alloc(layout) as *mut i32;
    if p.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    //@ from_u8s_(p);
    *p = 42;
    let v = *p;
    //@ to_u8s_(p);
    std::alloc::dealloc(p as *mut u8, layout);
}

// Splitting permission into [1/2] and [1/2] and reading from both
unsafe fn test_valid_fractional_read(p: *mut i32) -> i32
//@ req [1/2](*p) |-> ?v;
//@ ens [1/2](*p) |-> v &*& result == v;
{
    *p
}

// Recombining two [1/2] permissions into full permission and writing
unsafe fn test_valid_recombine(p: *mut i32)
//@ req [1/2](*p) |-> ?v1 &*& [1/2](*p) |-> ?v2;
//@ ens *p |-> 100;
{
    *p = 100;
}

// Swapping values through two distinct, non-aliasing pointers
unsafe fn test_valid_swap(p: *mut i32, q: *mut i32)
//@ req *p |-> ?v1 &*& *q |-> ?v2;
//@ ens *p |-> v2 &*& *q |-> v1;
{
    let tmp = *p;
    *p = *q;
    *q = tmp;
}

// =========================================================================
// NEGATIVE CASES: 12 should_fail cases
// =========================================================================

// 1. Reading a raw pointer without points-to permission
unsafe fn neg_read_without_perm(p: *mut i32) -> i32
//@ req true;
//@ ens true;
{
    *p //~should_fail
} //~allow_dead_code

// 2. Writing a raw pointer without points-to permission
unsafe fn neg_write_without_perm(p: *mut i32)
//@ req true;
//@ ens true;
{
    *p = 42; //~should_fail
} //~allow_dead_code

// 3. Writing through a fractional (read-only) points-to chunk [1/2]
unsafe fn neg_write_fractional(p: *mut i32)
//@ req [1/2](*p) |-> ?v;
//@ ens true;
{
    *p = 99; //~should_fail
} //~allow_dead_code

// 4. Consuming a points-to chunk twice (aliasing violation)
unsafe fn neg_consume_twice(p: *mut i32, q: *mut i32)
//@ req *p |-> 1;
//@ ens *p |-> 1 &*& *q |-> 1; //~should_fail
{
}

// 5. Use-after-free: reading a pointer after std::alloc::dealloc
unsafe fn neg_use_after_free_read()
//@ req true;
//@ ens true;
{
    let layout = std::alloc::Layout::new::<u8>();
    let p = std::alloc::alloc(layout);
    if p.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    *p = 42;
    std::alloc::dealloc(p, layout);
    let _v = *p; //~should_fail
} //~allow_dead_code

// 6. Use-after-free: writing through a pointer after std::alloc::dealloc
unsafe fn neg_use_after_free_write()
//@ req true;
//@ ens true;
{
    let layout = std::alloc::Layout::new::<u8>();
    let p = std::alloc::alloc(layout);
    if p.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    *p = 42;
    std::alloc::dealloc(p, layout);
    *p = 10; //~should_fail
} //~allow_dead_code

// 7. Double free: calling dealloc twice on the same allocation
unsafe fn neg_double_free()
//@ req true;
//@ ens true;
{
    let layout = std::alloc::Layout::new::<u8>();
    let p = std::alloc::alloc(layout);
    if p.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    *p = 42;
    std::alloc::dealloc(p, layout);
    std::alloc::dealloc(p, layout); //~should_fail
} //~allow_dead_code

// 8. Reading uninitialized memory allocated via std::alloc::alloc without from_u8s_
unsafe fn neg_read_uninit_without_from_u8s() -> i32
//@ req true;
//@ ens true;
{
    let layout = std::alloc::Layout::new::<i32>();
    let p = std::alloc::alloc(layout) as *mut i32;
    if p.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    *p //~should_fail
} //~allow_dead_code

// 9. Postcondition claiming unmodified value after write through aliased pointer
unsafe fn neg_aliased_write_false_post(p: *mut i32, q: *mut i32)
//@ req *p |-> 10 &*& p == q;
//@ ens *p |-> 10; //~should_fail
{
    *q = 20;
}

// 10. Consuming full permission when only half permission is available
unsafe fn neg_require_full_with_half(p: *mut i32)
//@ req [1/2](*p) |-> ?v;
//@ ens *p |-> v; //~should_fail
{
}

// 11. Passing aliased pointer to function requiring two disjoint points-to chunks
unsafe fn require_two_chunks(p: *mut i32, q: *mut i32)
//@ req *p |-> _ &*& *q |-> _;
//@ ens *p |-> _ &*& *q |-> _;
{}

unsafe fn neg_pass_aliased_to_disjoint(p: *mut i32)
//@ req *p |-> 5;
//@ ens true;
{
    require_two_chunks(p, p); //~should_fail
} //~allow_dead_code

// 12. Deallocating memory with mismatching layout size
unsafe fn neg_dealloc_mismatched_layout()
//@ req true;
//@ ens true;
{
    let layout1 = std::alloc::Layout::new::<u8>();
    let layout2 = std::alloc::Layout::new::<u64>();
    let p = std::alloc::alloc(layout1);
    if p.is_null() {
        std::alloc::handle_alloc_error(layout1);
    }
    *p = 7;
    std::alloc::dealloc(p, layout2); //~should_fail
} //~allow_dead_code

fn main() {}
