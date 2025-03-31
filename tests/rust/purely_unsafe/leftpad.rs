pub unsafe fn leftpad(c: u8, n: usize, ns: usize, s: *mut u8) -> usize
/*@
req s[..ns] |-> ?cs &*&
    if ns < n { (s + ns)[..n - ns] |-> _ } else { true };
@*/
/*@
ens s[..result - ns] |-> repeat(nat_of_int(result - ns), c) &*&
    (s + result - ns)[..ns] |-> cs;
@*/
//@ terminates;
{
    if ns < n {
        let p = n - ns;
        
        std::ptr::copy(s, s.add(p), ns);
        //@ div_rem_nonneg(s as usize, 1);
        std::ptr::write_bytes(s, c, p);
        n
    } else {
        ns
    }
}
