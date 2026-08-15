use std::ops::Deref;
fn main() {
    let x = Box::new(42u8);
    //================================================ κ begins
    let r = &x; // r: &'κ Box<u8>
    //====================================== κ1 begins, κ1 ⊑ κ
    let r_u8 = r.deref(); // r_u8: &'κ1 u8
    // r and r_u8 are simultaneously valid
    assert_eq!(*r, Box::new(42));
    assert_eq!(*r_u8, 42);
    //====================================== κ1 ends
    //================================================ κ ends => x unfreez
    // x drop
}