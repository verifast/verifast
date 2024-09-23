struct Foo {
    v: i32,
}

//@ pred_ctor my_fbc(t: thread_id_t, l: *Foo)() = false;
//@ type_pred_def <Foo>.full_borrow_content = my_fbc; //~should_fail
