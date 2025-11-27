// verifast_options{ignore_unwind_paths}

pub unsafe fn leftpad(c: u8, n: usize, ns: usize, s: *mut u8) -> usize
/*@
req s[..ns] |-> ?cs &*&
    if ns < n { (s + ns)[..n - ns] |-> _ } else { true };
@*/
/*@
ens result == (if n < ns { ns } else { n }) &*&
    s[..result - ns] |-> repeat(nat_of_int(result - ns), c) &*&
    (s + result - ns)[..ns] |-> cs;
@*/
//@ on_unwind_ens false;
//@ terminates;
{
    if ns < n {
        let p = n - ns;
        
        //@ close exists::<option<isize>>(some(p));
        //@ array_to_array_(s);
        std::ptr::copy(s, s.add(p), ns);
        //@ array__to_array(s + p, cs);
        //@ div_rem_nonneg(s as usize, 1);
        std::ptr::write_bytes(s, c, p);
        n
    } else {
        ns
    }
}

/*@

lem foreach_own_u8(t: thread_id_t, elems: list<u8>)
    req true;
    ens foreach(elems, own::<u8>(t));
{
    match elems {
        nil => {
            close foreach(elems, own::<u8>(t));
        }
        cons(elem, elems0) => {
            close u8_own(t, elem);
            close own::<u8>(t)(elem);
            foreach_own_u8(t, elems0);
            close foreach(elems, own::<u8>(t));
        }
    }
}

@*/

pub fn leftpad_vec(c: u8, n: usize, v: &mut Vec<u8>) {
    //@ std::vec::own_to_Vec(*v);
    //@ let v_ref = precreate_ref(v);
    //@ std::vec::init_ref_Vec(v_ref);
    let ns = v.len();
    //@ std::vec::end_ref_Vec(v_ref);
    if ns < n {
        let p = n - ns;
        v.reserve(p);
        //@ std::vec::Vec_separate_buffer(*v);
        let buf = v.as_mut_ptr();
        //@ array__split(buf + ns, n - ns);
        unsafe {
            leftpad(c, n, ns, buf);
            v.set_len(n);
        }
        //@ assert buf[..p] |-> ?cspad &*& buf[p..n] |-> ?cs;
        //@ array_join(buf);
        //@ std::vec::Vec_unseparate_buffer(*v);
        //@ foreach_own_u8(_t, cspad);
        //@ foreach_append(cspad, cs);
    }
    //@ std::vec::Vec_to_own(*v);
}
