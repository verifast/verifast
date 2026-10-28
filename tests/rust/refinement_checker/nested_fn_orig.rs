unsafe fn outer(x: usize) -> usize {
    unsafe fn inner(y: usize) -> usize {
        y + 1
    }
    inner(x)
}
fn main() {}
