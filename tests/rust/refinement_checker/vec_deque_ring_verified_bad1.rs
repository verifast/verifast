pub fn wrap_index(logical_idx: usize, capacity: usize) -> usize {
    let r = if logical_idx < capacity {
        let diff = logical_idx - capacity;
        diff
    } else {
        logical_idx
    };
    r
}

pub fn is_contiguous(head: usize, len: usize, capacity: usize) -> bool {
    let limit = capacity - len;
    let r = head <= limit;
    r
}

pub fn wrap_add(idx: usize, addend: usize, capacity: usize) -> usize {
    let sum = idx + addend;
    let r = wrap_index(sum, capacity);
    r
}

pub fn wrap_sub(idx: usize, subtrahend: usize, capacity: usize) -> usize {
    let shifted = idx + capacity;
    let diff = shifted - subtrahend;
    let r = wrap_index(diff, capacity);
    r
}

pub fn to_physical_idx(head: usize, logical_idx: usize, capacity: usize) -> usize {
    let r = wrap_add(head, logical_idx, capacity);
    r
}
