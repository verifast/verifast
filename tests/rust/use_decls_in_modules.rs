mod foo {
    //@ use std::option::Option;
    
    //@ fix quux() -> Option<i32>;

    fn bar() {
        //@ assert Option::None == Option::None;
    }

    //@ fix quux2() -> Option<i32>;
}
