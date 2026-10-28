unsafe fn outer(x: usize) -> usize
//@ req x < 100;
//@ ens result == x + 1;
{
    unsafe fn inner(y: usize) -> usize
    //@ req y < 100;
    //@ ens result == y + 1;
    {
        y + 1
    }
    inner(x)
}
fn main() {}
