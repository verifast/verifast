unsafe fn assert(b: bool)
//@ req b;
//@ ens true;
{
    if !b { //~allow_dead_code
        *std::ptr::null_mut() = 42; //~allow_dead_code
    }
}

enum MyOption {
    MyNone,
    MySome(i32)
}

unsafe fn eval(o: MyOption) -> i32
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
        assert(eval(MyOption::MyNone) == 0);
        assert(eval(MyOption::MySome(78)) == 78);
    }
}
