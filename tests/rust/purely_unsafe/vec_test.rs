// verifast_options{ignore_unwind_paths ignore_ref_creation}

unsafe fn assert(b: bool)
//@ req b;
//@ ens true;
{
    if !b { //~allow_dead_code
        let p = std::ptr::null_mut(); //~allow_dead_code
        *p = 42; //~allow_dead_code
    }
}

fn main() {
    unsafe {
        //@ assert thread_token(?t);
        let mut v = std::vec::Vec::<u8>::new();
        //@ close drop_perm::<u8>(false, True, _t, 10);
        v.push(10);
        //@ open drop_perm::<u8>(false, True, _t, 10);
        //@ close drop_perm::<u8>(false, True, _t, 20);
        v.push(20);
        //@ open drop_perm::<u8>(false, True, _t, 20);
        assert(v.len() == 2);
        //@ std::vec::Vec_separate_buffer(v);
        //@ open array(?buffer, 2, _);
        let v1 = *v.as_ptr();
        //@ open array(_, _, _);
        let v2 = *v.as_ptr().add(1);
        assert(v1 == 10);
        assert(v2 == 20);
        //@ close array(buffer + 1, 1, [20]);
        //@ close array(buffer, 2, [10, 20]);
        //@ std::vec::Vec_unseparate_buffer(v);
        //@ close u8_own(t, 10);
        //@ close own::<u8>(t)(10);
        //@ close u8_own(t, 20);
        //@ close own::<u8>(t)(20);
        //@ close foreach::<u8>([], own::<u8>(t));
        //@ close foreach::<u8>([20], own::<u8>(t));
        //@ close foreach::<u8>([10, 20], own::<u8>(t));
        //@ std::vec::Vec_to_own(v);
        std::mem::drop(v);
    }
}
