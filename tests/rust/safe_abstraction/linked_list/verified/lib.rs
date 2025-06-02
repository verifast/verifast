// verifast_options{skip_specless_fns ignore_unwind_paths}

#![no_std]
#![allow(internal_features)]
#![allow(incomplete_features)]
#![feature(allocator_api)]
#![feature(staged_api)]
#![feature(rustc_attrs)]
#![feature(dropck_eyepatch)]
#![feature(specialization)]
#![feature(extend_one)]
#![feature(exact_size_is_empty)]
#![feature(hasher_prefixfree_extras)]
#![feature(box_into_inner)]
#![feature(try_trait_v2)]

#![stable(feature = "rust1", since = "1.0.0")]

extern crate alloc as std;

#[stable(feature = "rust1", since = "1.0.0")]
pub use std::alloc as alloc;
#[stable(feature = "rust1", since = "1.0.0")]
pub use std::boxed as boxed;

trait SpecExtend<I> {
    fn spec_extend(&mut self, iter: I);
}

pub mod linked_list;
