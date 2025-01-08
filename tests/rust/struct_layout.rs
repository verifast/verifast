struct Foo {
    f1: i32,
    f2: i32,
}

fn main() {
    let f = Foo { f1: 42, f2: 24 };

    unsafe { std::hint::assert_unchecked(&raw const f as usize == &raw const f.f1 as usize); } //~should_fail
}
