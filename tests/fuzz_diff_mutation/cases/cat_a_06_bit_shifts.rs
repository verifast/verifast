// verifast_options{skip_specless_fns}
pub unsafe fn test_bit_shifts() -> (u8, i32)
//@ req true;
//@ ens true;
{
    let u: u8 = 255;
    let discarded: u8 = u << 4;
    let neg: i32 = -16;
    let arith: i32 = neg >> 2;
    (discarded, arith)
}
fn main() {}
