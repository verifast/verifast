unsafe fn outer(x: usize) -> usize
//@ req x < 100;
//@ ens result == x + 2;
{
    unsafe fn inner(y: usize) -> usize
    //@ req y < 100;
    //@ ens result == y + 2;
    {
        y + 2
    }
    inner(x)
}
fn main() {}
