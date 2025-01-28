struct Foo {
    f1: i32,
    f2: i32,
}

#[repr(C)]
struct Bar {
    f1: i32,
    f2: i32,
}

fn repr_c_test() {
    let b = Bar { f1: 42, f2: 24 };
    unsafe { std::hint::assert_unchecked(&raw const b.f1 == &raw const b as *const i32); }
}

fn repr_rust_test() {
    let f = Foo { f1: 42, f2: 24 };
    unsafe { std::hint::assert_unchecked(&raw const f as usize == &raw const f.f1 as usize); } //~should_fail
}