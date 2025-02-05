fn inc<'a>(b: &'a mut Box<u8>) {
    **b = **b + 1
}
fn main() {
    let mut x = Box::new(42);
    //======================= κ begins
    let r = &mut x; // borrow under κ
    inc(r);
    //======================= κ ends
    assert_eq!(*x, 43);
}
