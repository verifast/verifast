// verifast_options{ignore_ref_creation}

fn replace<'a, T>(r: &'a mut T, v: T) -> T {
    unsafe {
        //@ open_full_borrow(_q_a, 'a, (<T>.full_borrow_content)(_t, r));
        //@ open_full_borrow_content::<T>(_t, r);
        let result = std::ptr::read(r);
        std::ptr::write(r, v);
        //@ close_full_borrow_content::<T>(_t, r);
        //@ close_full_borrow(<T>.full_borrow_content(_t, r));
        //@ leak full_borrow(_, _);
        result
    }
}

fn swap<'a, T>(r1: &'a mut T, r2: &'a mut T) {
    unsafe {
        //@ open_full_borrow(_q_a/2, 'a, <T>.full_borrow_content(_t, r1));
        //@ open_full_borrow_content::<T>(_t, r1);
        //@ open_full_borrow(_q_a/2, 'a, <T>.full_borrow_content(_t, r2));
        //@ open_full_borrow_content::<T>(_t, r2);
        let tmp = std::ptr::read(r1);
        std::ptr::write(r1, std::ptr::read(r2));
        std::ptr::write(r2, tmp);
        //@ close_full_borrow_content::<T>(_t, r2);
        //@ close_full_borrow(<T>.full_borrow_content(_t, r2));
        //@ close_full_borrow_content::<T>(_t, r1);
        //@ close_full_borrow(<T>.full_borrow_content(_t, r1));
        //@ leak full_borrow(_, _);
        //@ leak full_borrow(_, _);
    }
}

fn share<'a, T>(r: &'a mut T) -> &'a T {
    //@ produce_type_interp::<T>();
    //@ share_full_borrow::<T>('a, _t, r);
    //@ leak type_interp();
    r
}
