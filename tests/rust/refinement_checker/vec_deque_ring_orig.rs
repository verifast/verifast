pub fn wrap_index(logical_idx: usize, capacity: usize) -> usize {
    if logical_idx >= capacity {
        logical_idx - capacity
    } else {
        logical_idx
    }
}

pub fn is_contiguous(head: usize, len: usize, capacity: usize) -> bool {
    head <= capacity - len
}

pub fn wrap_add(idx: usize, addend: usize, capacity: usize) -> usize {
    wrap_index(idx + addend, capacity)
}

pub fn wrap_sub(idx: usize, subtrahend: usize, capacity: usize) -> usize {
    wrap_index((idx + capacity) - subtrahend, capacity)
}

pub fn to_physical_idx(head: usize, logical_idx: usize, capacity: usize) -> usize {
    wrap_add(head, logical_idx, capacity)
}
