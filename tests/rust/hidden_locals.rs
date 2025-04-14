fn main() {
    unsafe {
        let mut x = 10;
        x += 1;
        {
            let x = 20;
            //@ assert x == 11 && x_1 == 20;
            let x = 30;
            //@ assert x == 11 && x_1 == 20 && x_2 == 30;
        }
        x += 1;
        //@ assert x == 12;
    }
}
