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

/*@
lem foreach_own_u8(t: thread_id_t, elems: list<u8>)
    req true;
    ens foreach(elems, own::<u8>(t));
{
    match elems {
        nil => {
            close foreach(elems, own::<u8>(t));
        }
        cons(elem, elems0) => {
            close u8_own(t, elem);
            close own::<u8>(t)(elem);
            foreach_own_u8(t, elems0);
            close foreach(elems, own::<u8>(t));
        }
    }
}
@*/

fn array_roundtrip(xs: [u8; 3]) -> [u8; 3] {
    xs
}

fn consume(_xs: [u8; 3]) {
    //@ leak <[u8; 3]>.own(_, _xs);
}

fn test4() {
    let xs: [u8; 3] = [1, 2, 3];
    //@ let xs_val = xs;
    //@ foreach_own_u8(currentThread, Array_elems(xs_val));
    //@ close <[u8; 3]>.own(currentThread, xs_val);
    let ys = array_roundtrip(xs);
    consume(ys);
}

fn main() {
    test1();
    test2();
    test4();
}
