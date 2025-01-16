// verifast_options{ignore_unwind_paths}

unsafe fn assert(b: bool)
//@ req b;
//@ ens true;
{}

fn test_alloc_i8()
{
    unsafe {
        let layout = std::alloc::Layout::new::<i8>();
        let p = std::alloc::alloc(layout) as *mut i8;
        if p.is_null() {
            std::alloc::handle_alloc_error(layout);
        }
        //@ from_u8s_(p);
        *p = -42;
        //@ assert *p |-> ?v &*& v == -42;
        assert(*p == -42);
        //@ to_u8s_(p);
        std::alloc::dealloc(p as *mut u8, layout);
    }
}

fn test_alloc_i16()
{
    unsafe {
        let layout = std::alloc::Layout::new::<i16>();
        let p = std::alloc::alloc(layout) as *mut i16;
        if p.is_null() {
            std::alloc::handle_alloc_error(layout);
        }
        //@ from_u8s_(p);
        *p = -10000;
        //@ assert *p |-> ?v &*& v == -10000;
        assert(*p == -10000);
        //@ to_u8s_(p);
        std::alloc::dealloc(p as *mut u8, layout);
    }
}

fn test_alloc_i32()
{
    unsafe {
        let layout = std::alloc::Layout::new::<i32>();
        let p = std::alloc::alloc(layout) as *mut i32;
        if p.is_null() {
            std::alloc::handle_alloc_error(layout);
        }
        //@ from_u8s_(p);
        *p = -1_000_000_000;
        //@ assert *p |-> ?v &*& v == -1000000000;
        assert(*p == -1_000_000_000);
        //@ to_u8s_(p);
        std::alloc::dealloc(p as *mut u8, layout);
    }
}

fn test_alloc_i64()
{
    unsafe {
        let layout = std::alloc::Layout::new::<i64>();
        let p = std::alloc::alloc(layout) as *mut i64;
        if p.is_null() {
            std::alloc::handle_alloc_error(layout);
        }
        //@ from_u8s_(p);
        *p = -1_000_000_000_000_000_000;
        //@ assert *p |-> ?v1 &*& v1 == -1000000000000000000;
        assert(*p == -1_000_000_000_000_000_000);
        *p = -2305843009213693952;
        //@ assert *p |-> ?v2 &*& v2 == -2305843009213693952;
        assert(*p == -2305843009213693952);
        *p = -9223372036854775807;
        //@ assert *p |-> ?v3 &*& v3 == -9223372036854775807;
        assert(*p == -9223372036854775807);
        //@ to_u8s_(p);
        std::alloc::dealloc(p as *mut u8, layout);
    }
}

fn test_alloc_i128()
{
    unsafe {
        let layout = std::alloc::Layout::new::<i128>();
        let p = std::alloc::alloc(layout) as *mut i128;
        if p.is_null() {
            std::alloc::handle_alloc_error(layout);
        }
        //@ from_u8s_(p);
        *p = -36893488147419103231i128;
        //@ assert *p |-> ?v1 &*& v1 == -36893488147419103231;
        assert(*p == -36893488147419103231i128);
        *p = -36893488147419103230i128;
        //@ assert *p |-> ?v2 &*& v2 == -36893488147419103230;
        assert(*p == -36893488147419103230i128);
        //@ to_u8s_(p);
        std::alloc::dealloc(p as *mut u8, layout);
    }
}

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
        assert(*p == 42);
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
        //@ from_u8s_(p);
        *p = 10000;
        //@ assert *p |-> ?v &*& v == 10000;
        assert(*p == 10000);
        //@ to_u8s_(p);
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
        //@ from_u8s_(p);
        *p = 1_000_000_000;
        //@ assert *p |-> ?v &*& v == 1000000000;
        assert(*p == 1_000_000_000);
        //@ to_u8s_(p);
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
        //@ from_u8s_(p);
        *p = 1_000_000_000_000_000_000;
        //@ assert *p |-> ?v1 &*& v1 == 1000000000000000000;
        assert(*p == 1_000_000_000_000_000_000);
        *p = 18446744073709551615;
        //@ assert *p |-> ?v2 &*& v2 == 18446744073709551615;
        assert(*p == 18446744073709551615);
        *p = 9223372036854775808;
        //@ assert *p |-> ?v3 &*& v3 == 9223372036854775808;
        assert(*p == 9223372036854775808);
        *p = 9223372036854775809;
        //@ assert *p |-> ?v4 &*& v4 == 9223372036854775809;
        assert(*p == 9223372036854775809);
        //@ to_u8s_(p);
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
        //@ from_u8s_(p);
        *p = 36893488147419103231u128;
        //@ assert *p |-> ?v1 &*& v1 == 36893488147419103231;
        assert(*p == 36893488147419103231u128);
        *p = 36893488147419103230u128;
        //@ assert *p |-> ?v2 &*& v2 == 36893488147419103230;
        assert(*p == 36893488147419103230u128);
        *p = 340282366920938463463374607431768211455u128;
        //@ assert *p |-> ?v3 &*& v3 == 340282366920938463463374607431768211455;
        assert(*p == 340282366920938463463374607431768211455u128);
        //@ to_u8s_(p);
        std::alloc::dealloc(p as *mut u8, layout);
    }
}
