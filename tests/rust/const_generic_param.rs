// verifast_options{skip_specless_fns}

use std::mem::MaybeUninit;

fn foo<T, const N: usize>() {
    let zs: [MaybeUninit<T>; N] = unsafe { MaybeUninit::uninit().assume_init() };
    let r = &zs;
}
