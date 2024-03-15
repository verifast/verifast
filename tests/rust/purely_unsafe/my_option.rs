unsafe fn assert(b: bool)
//@ req b;
//@ ens true;
{
    if !b { //~allow_dead_code
        *std::ptr::null_mut() = 42; //~allow_dead_code
    }
}

enum MyOptionI32 {
    MyNoneI32,
    MySomeI32(i32)
}

unsafe fn eval_i32(o: MyOptionI32) -> i32
//@ req true;
//@ ens result == match o { MyNoneI32 => 0, MySomeI32(v) => v };
{
    match o {
        MyOptionI32::MyNoneI32 => 0,
        MyOptionI32::MySomeI32(v) => v
    }
}

enum MyOption<T> {
    MyNone,
    MySome(T)
}

unsafe fn eval(o: MyOption<i32>) -> i32
//@ req true;
//@ ens result == match o { MyNone => 0, MySome(v) => v };
{
    match o {
        MyOption::MyNone => 0,
        MyOption::MySome(v) => v
    }
}


fn main() {
    unsafe {
        assert(eval_i32(MyOptionI32::MyNoneI32) == 0);
        assert(eval_i32(MyOptionI32::MySomeI32(78)) == 78);
        
        assert(eval(MyOption::MyNone) == 0);
        assert(eval(MyOption::MySome(78)) == 78);
    }
}
