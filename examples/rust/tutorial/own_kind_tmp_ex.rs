fn inc<'a>(b: &'a mut Box<u8>) { **b = **b + 1; }

fn main() {
    let mut x = Box::new(42);
    //====================================== κ begins
    let r = &mut x; // borrow under κ
    // assert_eq!(*x, 42); // is not allowed by compoiler
    inc(r);
    //====================================== κ ends => x unfreez
    assert_eq!(*x, 43);
    // x drop
}
