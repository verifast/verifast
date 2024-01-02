// Some Unicode characters, to test the preprocessor: risqué 你好 😄

unsafe fn assert(_b: bool)
//@ req _b;
//@ ens true;
{
    if !_b { //~allow_dead_code
        assert(_b); //~allow_dead_code // Cause stack overflow
    }
}

trait Adder {

    unsafe fn add(x: i32, y: i32) -> i32
    //@ req -0x80000000 <= x + y &*& x + y <= 0x7fffffff;
    //@ ens result == x + y;
    {
        Self::add(x, y)
    }

    unsafe fn subtract(x: i32, y: i32) -> i32;
    //@ req x - y <= 0x7fffffff;
    //@ ens result == x - y;

}

unsafe fn double<T: Adder>(a: i32) -> i32
//@ req -0x80000000 <= a + a &*& a + a <= 0x7fffffff;
//@ ens result == a + a;
{
    T::add(T::add(a, a), T::subtract(a, a))
}

struct MyAdder;

impl Adder for MyAdder {

    unsafe fn add(x: i32, y: i32) -> i32
    //@ req -0x80000000 <= x + y &*& x + y <= 0x7fffffff;
    //@ ens result == x + y;
    {
        x + y
    }

    unsafe fn subtract(x: i32, y: i32) -> i32
    //@ req 0x8000000 <= x - y &*& x - y <= 0x7fffffff; //~should_fail
    //@ ens result == x - y;
    {
        x - y
    }

}

fn main() {
    unsafe {
        let x = MyAdder::add(100, 200);
        assert(x == 300);

        let d = double::<MyAdder>(42);
        assert(d == 84);
    }
}
