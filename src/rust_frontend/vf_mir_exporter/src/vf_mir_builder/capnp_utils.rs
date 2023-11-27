use crate::vf_mir_capnp;
use util_cpn::int128 as int128_cpn;
use util_cpn::u_int128 as u_int128_cpn;
use vf_mir_capnp::util as util_cpn;

pub fn encode_int128(v: i128, mut v_cpn: int128_cpn::Builder<'_>) {
    let le_bytes = v.to_le_bytes();
    // TODO @Nima: After stabilization of split_array functions we can change the following calls to one
    let (lo, _) = le_bytes.split_array_ref::<8>();
    let (_, hi) = le_bytes.rsplit_array_ref::<8>();
    let lo = u64::from_le_bytes(*lo);
    let hi = i64::from_le_bytes(*hi);
    v_cpn.set_l(lo);
    v_cpn.set_h(hi);
}

pub fn encode_u_int128(v: u128, mut v_cpn: u_int128_cpn::Builder<'_>) {
    let le_bytes = v.to_le_bytes();
    // TODO @Nima: After stabilization of split_array functions we can change the following calls to one
    let (lo, _) = le_bytes.split_array_ref::<8>();
    let (_, hi) = le_bytes.rsplit_array_ref::<8>();
    let lo = u64::from_le_bytes(*lo);
    let hi = u64::from_le_bytes(*hi);
    v_cpn.set_l(lo);
    v_cpn.set_h(hi);
}
