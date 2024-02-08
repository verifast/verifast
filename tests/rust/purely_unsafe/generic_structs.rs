struct Pair<A, B> {
    fst: A,
    snd: B
}

unsafe fn swap_Pair_i32_bool(p1: *mut Pair<i32, bool>, p2: *mut Pair<i32, bool>)
//@ req (*p1).fst |-> ?fst1 &*& (*p1).snd |-> ?snd1 &*& (*p2).fst |-> ?fst2 &*& (*p2).snd |-> ?snd2;
//@ ens (*p1).fst |-> fst2 &*& (*p1).snd |-> snd2 &*& (*p2).fst |-> fst1 &*& (*p2).snd |-> snd1;
{
    let tmp1 = (*p1).fst;
    let tmp2 = (*p1).snd;
    (*p1).fst = (*p2).fst;
    (*p1).snd = (*p2).snd;
    (*p2).fst = tmp1;
    (*p2).snd = tmp2;
}
