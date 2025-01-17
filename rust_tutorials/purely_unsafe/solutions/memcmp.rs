unsafe fn memcmp(p1: *const u8, p2: *const u8, count: usize) -> i32
//@ req [?f1]p1[0..count] |-> ?cs1 &*& [?f2]p2[0..count] |-> ?cs2;
//@ ens [f1]p1[0..count] |-> cs1 &*& [f2]p2[0..count] |-> cs2 &*& (result == 0) == (cs1 == cs2);
{
    let mut result = 0;
    let mut i = 0;
    //@ let result_ = 0;
    loop {
        /*@
        req [f1]p1[i..count] |-> ?xs1 &*& [f2]p2[i..count] |-> ?xs2 &*& result == 0 &*& result_ == 0;
        ens [f1]p1[old_i..count] |-> xs1 &*& [f2]p2[old_i..count] |-> xs2 &*& result == 0 &*& (result_ == 0) == (xs1 == xs2);
        @*/
        //@ open array(p1 + i, _, _);
        //@ open array(p2 + i, _, _);
        if i == count {
            break;
        }
        //@ if p1[i] < p2[i] { result_ = -1; }
        if *p1.add(i) < *p2.add(i) {
            result = -1;
            break;
        }
        //@ if p1[i] > p2[i] { result_ = 1; }
        if *p1.add(i) > *p2.add(i) {
            result = 1;
            break;
        }
        i += 1;
    }
    result
}
