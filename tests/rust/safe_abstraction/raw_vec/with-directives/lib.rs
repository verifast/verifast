// verifast_options{skip_specless_fns}

#![allow(dead_code)]
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
#![feature(optimize_attribute)]
#![feature(temporary_niche_types)]
#![feature(ptr_internals)]
#![feature(try_reserve_kind)]
#![feature(ptr_alignment_type)]
#![feature(sized_type_properties)]
#![feature(std_internals)]
#![feature(alloc_layout_extra)]
#![feature(nonnull_provenance)]
#![feature(panic_internals)]

#![stable(feature = "rust1", since = "1.0.0")]

extern crate alloc as std;

#[stable(feature = "rust1", since = "1.0.0")]
pub use std::alloc as alloc;
#[stable(feature = "rust1", since = "1.0.0")]
pub use std::boxed as boxed;
#[stable(feature = "rust1", since = "1.0.0")]
pub use std::collections as collections;

pub mod raw_vec;
