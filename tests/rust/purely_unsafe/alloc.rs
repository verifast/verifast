fn main()
{
    unsafe {
        let layout = std::alloc::Layout::new::<u8>();
        let p = std::alloc::alloc(layout);
        if p.is_null() {
            std::alloc::handle_alloc_error(layout);
        }
        *p = 42;
        //@ assert *p |-> ?v &*& v == 42;
        if *p != 42 {
            std::alloc::dealloc(p, layout);
            std::alloc::dealloc(p, layout);
        }
        std::alloc::dealloc(p, layout);
    }
}

fn test_alloc_u16()
{
    unsafe {
        let layout = std::alloc::Layout::new::<u16>();
        let p = std::alloc::alloc(layout) as *mut u16;
        if p.is_null() {
            std::alloc::handle_alloc_error(layout);
        }
        //@ u8s__to_integer__(p, 2, false);
        *p = 10000;
        //@ assert *p |-> ?v &*& v == 10000;
        if *p != 10000 {
            std::alloc::dealloc(p as *mut u8, layout);
            std::alloc::dealloc(p as *mut u8, layout);
        }
        //@ integer__to_u8s(p, 2, false);
        std::alloc::dealloc(p as *mut u8, layout);
    }
}

fn test_alloc_u32()
{
    unsafe {
        let layout = std::alloc::Layout::new::<u32>();
        let p = std::alloc::alloc(layout) as *mut u32;
        if p.is_null() {
            std::alloc::handle_alloc_error(layout);
        }
        //@ u8s__to_integer__(p, 4, false);
        *p = 1_000_000_000;
        //@ assert *p |-> ?v &*& v == 1000000000;
        if *p != 1_000_000_000 {
            std::alloc::dealloc(p as *mut u8, layout);
            std::alloc::dealloc(p as *mut u8, layout);
        }
        //@ integer__to_u8s(p, 4, false);
        std::alloc::dealloc(p as *mut u8, layout);
    }
}

fn test_alloc_u64()
{
    unsafe {
        let layout = std::alloc::Layout::new::<u64>();
        let p = std::alloc::alloc(layout) as *mut u64;
        if p.is_null() {
            std::alloc::handle_alloc_error(layout);
        }
        //@ u8s__to_integer__(p, 8, false);
        *p = 1_000_000_000_000_000_000;
        //@ assert *p |-> ?v1 &*& v1 == 1000000000000000000;
        if *p != 1_000_000_000_000_000_000 {
            std::alloc::dealloc(p as *mut u8, layout);
            std::alloc::dealloc(p as *mut u8, layout);
        }
        *p = 18446744073709551615;
        //@ assert *p |-> ?v2 &*& v2 == 18446744073709551615;
        if *p != 18446744073709551615 {
            std::alloc::dealloc(p as *mut u8, layout);
            std::alloc::dealloc(p as *mut u8, layout);
        }
        *p = 9223372036854775808;
        //@ assert *p |-> ?v3 &*& v3 == 9223372036854775808;
        if *p != 9223372036854775808 {
            std::alloc::dealloc(p as *mut u8, layout);
            std::alloc::dealloc(p as *mut u8, layout);
        }
        *p = 9223372036854775809;
        //@ assert *p |-> ?v4 &*& v4 == 9223372036854775809;
        if *p != 9223372036854775809 {
            std::alloc::dealloc(p as *mut u8, layout);
            std::alloc::dealloc(p as *mut u8, layout);
        }
        //@ integer__to_u8s(p, 8, false);
        std::alloc::dealloc(p as *mut u8, layout);
    }
}

fn test_alloc_u128()
{
    unsafe {
        let layout = std::alloc::Layout::new::<u128>();
        let p = std::alloc::alloc(layout) as *mut u128;
        if p.is_null() {
            std::alloc::handle_alloc_error(layout);
        }
        //@ u8s__to_integer__(p, 16, false);
        *p = 36893488147419103231u128;
        //@ assert *p |-> ?v1 &*& v1 == 36893488147419103231;
        if *p != 36893488147419103231u128 {
            std::alloc::dealloc(p as *mut u8, layout);
            std::alloc::dealloc(p as *mut u8, layout);
        }
        *p = 36893488147419103230u128;
        //@ assert *p |-> ?v2 &*& v2 == 36893488147419103230;
        if *p != 36893488147419103230u128 {
            std::alloc::dealloc(p as *mut u8, layout);
            std::alloc::dealloc(p as *mut u8, layout);
        }
        *p = 340282366920938463463374607431768211455u128;
        //@ assert *p |-> ?v3 &*& v3 == 340282366920938463463374607431768211455;
        if *p != 340282366920938463463374607431768211455u128 {
            std::alloc::dealloc(p as *mut u8, layout);
            std::alloc::dealloc(p as *mut u8, layout);
        }
        //@ integer__to_u8s(p, 16, false);
        std::alloc::dealloc(p as *mut u8, layout);
    }
}
