// Specifications on `fn` items nested inside a function body.

unsafe fn outer(x: usize) -> usize
//@ req x < 100;
//@ ens result == x + 1;
{
    unsafe fn inner(y: usize) -> usize
    //@ req y < 100;
    //@ ens result == y + 1;
    {
        y + 1
    }
    inner(x)
}

// A nested fn with raw-pointer parameters and a points-to specification.
unsafe fn swap_both(a: *mut u8, b: *mut u8)
//@ req *a |-> ?va &*& *b |-> ?vb;
//@ ens *a |-> vb &*& *b |-> va;
{
    unsafe fn swap_ptrs(x: *mut u8, y: *mut u8)
    //@ req *x |-> ?vx &*& *y |-> ?vy;
    //@ ens *x |-> vy &*& *y |-> vx;
    {
        let t = std::ptr::read(x);
        let u = std::ptr::read(y);
        std::ptr::write(x, u);
        std::ptr::write(y, t);
    }
    swap_ptrs(a, b);
}

// A generic nested fn inside a generic fn (the shape of `<[T]>::reverse`'s `revswap`).
unsafe fn pass_through<T>(x: T) -> T
//@ req true;
//@ ens true;
{
    unsafe fn identity<T>(y: T) -> T
    //@ req true;
    //@ ens true;
    {
        y
    }
    identity(x)
}

fn main() {}
