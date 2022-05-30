pub struct Cell_i32 {
    value: i32
}

/*@

pred Cell_i32_nonatomic_borrow_content(l: *i32, t: thread_id)() =
  *l |-> _;

interp Cell_i32 {
  pred shared(k: lifetime, t: thread_id, l: *i32) = nonatomic_borrow(k, t, l, Cell_i32_nonatomic_borrow_content(l, t));
}

@*/

impl Cell_i32 {
    fn replace(&self, val: i32) -> i32
    //@ req [?q]lifetime(?a) &*& Cell_i32_shared(a, ?t, self) &*& thread_token(t);
    //@ ens [q]lifetime(a) &*& thread_token(t);
    {
        //@ open Cell_i32_shared(a, t, self);
        //@ open_nonatomic_borrow(a, t, self, q);
        //@ open Cell_i32_nonatomic_borrow_content(self, t)();
        let result: i32 = self.value;
        self.value = val; // using unsafe superpower
        //@ close Cell_i32_nonatomic_borrow_content(self, t)();
        //@ close_nonatomic_borrow();
        return result;
    }
}
