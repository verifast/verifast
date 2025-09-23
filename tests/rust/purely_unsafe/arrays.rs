use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

const N: usize = 1;

fn test1() {
    unsafe {
        let xs: [i32; 2 * N + 1] = [10, 20, 30];
        let mut sum = 0;
        let p: *const i32 = &raw const xs as *const i32;
        sum += *p;
        sum += *p.add(1);
        sum += *p.add(2);
        std::hint::assert_unchecked(sum == 60);
        //@ close [1/2]array_(p + 2, 1, _);
        //@ close [1/2]array_(p + 1, 2, _);
        //@ close [1/2]array_(p, 3, _);
    }
}

struct Foo {
    xs: [i32; 2 * N + 1],
    y: i32
}

fn test2() {
    unsafe {
        let foo = alloc(Layout::new::<Foo>()) as *mut Foo;
        if foo.is_null() {
            handle_alloc_error(Layout::new::<Foo>());
        }
        let p: *mut i32 = &raw mut (*foo).xs as *mut i32;
        *p = 10;
        *p.add(1) = 20;
        *p.add(2) = 30;
        
        let mut sum = 0;
        sum += *p;
        sum += *p.add(1);
        sum += *p.add(2);
        std::hint::assert_unchecked(sum == 60);
        //@ close array_(p + 2, 1, _);
        //@ close array_(p + 1, 2, _);
        //@ close array_(p, 3, _);
        dealloc(foo as *mut u8, Layout::new::<Foo>());
    }
}

unsafe fn test3(xs: *mut [i32; 3])
//@ req *xs |-> Array_of_elems::<i32, 3>([10, 20, 30]);
//@ ens *xs |-> Array_of_elems::<i32, 3>([30, 20, 10]);
{
    //@ Array_to_array(xs);
    let p = xs as *mut i32;
    *p = 30;
    *p.add(1) = 20;
    *p.add(2) = 10;
    //@ open array(p + 3, 0, _);
    //@ close array(p + 3, 0, []);
    //@ array_to_Array(xs);
}

fn main() {
    test1();
    test2();
}
