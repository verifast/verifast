// verifast_options{skip_specless_fns}

pub struct RingBuffer {
    raw: *mut [u8],
    head: usize,
    len: usize,
    cap: usize,
}

/*@
pred RingBuffer_pred(rb: *RingBuffer; raw: *[u8], head: usize, len: usize, cap: usize) =
    (*rb).raw |-> raw &*&
    (*rb).head |-> head &*&
    (*rb).len |-> len &*&
    (*rb).cap |-> cap &*&
    0 < cap &*&
    head < cap &*&
    len <= cap;
@*/

unsafe fn wrap_index(logical_idx: usize, capacity: usize) -> usize
//@ req capacity > 0 &*& (logical_idx < capacity || logical_idx - capacity < capacity);
//@ ens result < capacity &*& if logical_idx < capacity { result == logical_idx } else { result == logical_idx - capacity };
{
    if logical_idx >= capacity {
        logical_idx - capacity
    } else {
        logical_idx
    }
}

unsafe fn wrap_add(idx: usize, addend: usize, capacity: usize) -> usize
//@ req capacity > 0 &*& idx < capacity &*& addend <= capacity;
//@ ens result < capacity;
{
    if addend < capacity - idx {
        idx + addend
    } else {
        addend - (capacity - idx)
    }
}

unsafe fn wrap_sub(idx: usize, subtrahend: usize, capacity: usize) -> usize
//@ req capacity > 0 &*& idx < capacity &*& subtrahend <= capacity;
//@ ens result < capacity;
{
    if idx >= subtrahend {
        idx - subtrahend
    } else {
        capacity - (subtrahend - idx)
    }
}

unsafe fn to_physical_idx(head: usize, logical_idx: usize, capacity: usize) -> usize
//@ req capacity > 0 &*& head < capacity &*& logical_idx < capacity;
//@ ens result < capacity;
{
    if logical_idx < capacity - head {
        head + logical_idx
    } else {
        logical_idx - (capacity - head)
    }
}

unsafe fn is_contiguous(head: usize, len: usize, capacity: usize) -> bool
//@ req len <= capacity &*& head < capacity;
//@ ens result == (head <= capacity - len);
{
    head <= capacity - len
}

unsafe fn rb_len(rb: *mut RingBuffer) -> usize
//@ req RingBuffer_pred(rb, ?raw, ?head, ?len, ?cap);
//@ ens RingBuffer_pred(rb, raw, head, len, cap) &*& result == len;
{
    //@ open RingBuffer_pred(rb, raw, head, len, cap);
    let l = (*rb).len;
    //@ close RingBuffer_pred(rb, raw, head, len, cap);
    l
}

unsafe fn rb_is_empty(rb: *mut RingBuffer) -> bool
//@ req RingBuffer_pred(rb, ?raw, ?head, ?len, ?cap);
//@ ens RingBuffer_pred(rb, raw, head, len, cap) &*& result == (len == 0);
{
    //@ open RingBuffer_pred(rb, raw, head, len, cap);
    let res = (*rb).len == 0;
    //@ close RingBuffer_pred(rb, raw, head, len, cap);
    res
}

unsafe fn rb_clear(rb: *mut RingBuffer)
//@ req RingBuffer_pred(rb, ?raw, ?head, ?len, ?cap);
//@ ens RingBuffer_pred(rb, raw, 0, 0, cap);
{
    //@ open RingBuffer_pred(rb, raw, head, len, cap);
    (*rb).head = 0;
    (*rb).len = 0;
    //@ close RingBuffer_pred(rb, raw, 0, 0, cap);
}

unsafe fn rb_front_idx(rb: *mut RingBuffer) -> usize
//@ req RingBuffer_pred(rb, ?raw, ?head, ?len, ?cap) &*& 0 < len;
//@ ens RingBuffer_pred(rb, raw, head, len, cap) &*& result == head &*& result < cap;
{
    //@ open RingBuffer_pred(rb, raw, head, len, cap);
    let f = (*rb).head;
    //@ close RingBuffer_pred(rb, raw, head, len, cap);
    f
}

unsafe fn rb_back_idx(rb: *mut RingBuffer) -> usize
//@ req RingBuffer_pred(rb, ?raw, ?head, ?len, ?cap) &*& 0 < len;
//@ ens RingBuffer_pred(rb, raw, head, len, cap) &*& result < cap;
{
    //@ open RingBuffer_pred(rb, raw, head, len, cap);
    let h = (*rb).head;
    let l = (*rb).len;
    let c = (*rb).cap;
    let offset = l - 1;
    let b = if offset < c - h {
        h + offset
    } else {
        offset - (c - h)
    };
    //@ close RingBuffer_pred(rb, raw, head, len, cap);
    b
}

unsafe fn rb_get_physical_idx(rb: *mut RingBuffer, logical_idx: usize) -> usize
//@ req RingBuffer_pred(rb, ?raw, ?head, ?len, ?cap) &*& logical_idx < len;
//@ ens RingBuffer_pred(rb, raw, head, len, cap) &*& result < cap;
{
    //@ open RingBuffer_pred(rb, raw, head, len, cap);
    let h = (*rb).head;
    let c = (*rb).cap;
    let phys = if logical_idx < c - h {
        h + logical_idx
    } else {
        logical_idx - (c - h)
    };
    //@ close RingBuffer_pred(rb, raw, head, len, cap);
    phys
}

unsafe fn rb_get_raw(rb: *mut RingBuffer) -> *mut [u8]
//@ req RingBuffer_pred(rb, ?raw, ?head, ?len, ?cap);
//@ ens RingBuffer_pred(rb, raw, head, len, cap) &*& result == raw;
{
    //@ open RingBuffer_pred(rb, raw, head, len, cap);
    let r = (*rb).raw;
    //@ close RingBuffer_pred(rb, raw, head, len, cap);
    r
}

unsafe fn rb_set_raw(rb: *mut RingBuffer, new_raw: *mut [u8])
//@ req RingBuffer_pred(rb, ?raw, ?head, ?len, ?cap);
//@ ens RingBuffer_pred(rb, new_raw, head, len, cap);
{
    //@ open RingBuffer_pred(rb, raw, head, len, cap);
    (*rb).raw = new_raw;
    //@ close RingBuffer_pred(rb, new_raw, head, len, cap);
}

// Negative tests verifying that contracts catch out-of-bounds and invalid states

unsafe fn bad_head_ge_capacity(head: usize, capacity: usize) -> usize
//@ req head >= capacity &*& capacity > 0;
//@ ens true;
{
    wrap_add(head, 0, capacity) //~should_fail
} //~allow_dead_code

unsafe fn bad_contiguous_underflow(head: usize, len: usize, capacity: usize) -> bool
//@ req len > capacity &*& head < capacity;
//@ ens true;
{
    is_contiguous(head, len, capacity) //~should_fail
} //~allow_dead_code

unsafe fn bad_logical_idx_ge_len(rb: *mut RingBuffer) -> usize
//@ req RingBuffer_pred(rb, ?raw, ?head, ?len, ?cap);
//@ ens RingBuffer_pred(rb, raw, head, len, cap);
{
    //@ open RingBuffer_pred(rb, raw, head, len, cap);
    let l = (*rb).len;
    //@ close RingBuffer_pred(rb, raw, head, len, cap);
    rb_get_physical_idx(rb, l) //~should_fail
} //~allow_dead_code

unsafe fn bad_back_on_empty(rb: *mut RingBuffer) -> usize
//@ req RingBuffer_pred(rb, ?raw, ?head, 0, ?cap);
//@ ens RingBuffer_pred(rb, raw, head, 0, cap);
{
    rb_back_idx(rb) //~should_fail
} //~allow_dead_code

fn bad_forge_slice<'a>(p: *mut [u8]) -> &'a mut [u8] { //~should_fail
    unsafe { &mut *p }
} //~allow_dead_code

fn main() {}
