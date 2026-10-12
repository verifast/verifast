// verifast_options{ignore_ref_creation disable_overflow_check}

// Regression test for the Range<T> IntoIterator/Iterator specs with non-usize
// integer element types. Without the specs in lib.rsspec, `it.next()` fails in
// the frontend (Type mismatch on <Range<u8> as Iterator>::Item, or for a `for`
// loop: No such function: std::iter::IntoIterator::into_iter). With them, next()
// resolves to a concrete impl method and the functions below verify.
//
// count_u8_range exercises into_iter + a full next() loop (usability).
// first_<T> pins the next() postcondition symbolically for every added type:
// the first element of a nonempty range is `start`; an empty range yields None
// (reported here via the sentinel 77, which is in range for all these types).

unsafe fn count_u8_range(end: u8) -> usize
//@ req true;
//@ ens true;
//@ on_unwind_ens false;
{
    let r = std::ops::Range { start: 0u8, end };
    let mut it = r.into_iter();
    let mut result: usize = 0;
    loop {
        /*@
        req it |-> ?r0;
        ens it |-> _;
        @*/
        let it_ref = &mut it;
        let i_opt = it_ref.next();
        match i_opt {
            None => break,
            Some(_v) => {
                result += 1;
            }
        }
    }
    result
}

unsafe fn first_u8(start: u8, end: u8) -> u8
//@ req true;
//@ ens if start < end { result == start } else { result == 77 };
//@ on_unwind_ens false;
{ let mut it = start..end; let r = &mut it; match r.next() { None => 77, Some(v) => v } }

unsafe fn first_u16(start: u16, end: u16) -> u16
//@ req true;
//@ ens if start < end { result == start } else { result == 77 };
//@ on_unwind_ens false;
{ let mut it = start..end; let r = &mut it; match r.next() { None => 77, Some(v) => v } }

unsafe fn first_u32(start: u32, end: u32) -> u32
//@ req true;
//@ ens if start < end { result == start } else { result == 77 };
//@ on_unwind_ens false;
{ let mut it = start..end; let r = &mut it; match r.next() { None => 77, Some(v) => v } }

unsafe fn first_u64(start: u64, end: u64) -> u64
//@ req true;
//@ ens if start < end { result == start } else { result == 77 };
//@ on_unwind_ens false;
{ let mut it = start..end; let r = &mut it; match r.next() { None => 77, Some(v) => v } }

unsafe fn first_u128(start: u128, end: u128) -> u128
//@ req true;
//@ ens if start < end { result == start } else { result == 77 };
//@ on_unwind_ens false;
{ let mut it = start..end; let r = &mut it; match r.next() { None => 77, Some(v) => v } }

unsafe fn first_i8(start: i8, end: i8) -> i8
//@ req true;
//@ ens if start < end { result == start } else { result == 77 };
//@ on_unwind_ens false;
{ let mut it = start..end; let r = &mut it; match r.next() { None => 77, Some(v) => v } }

unsafe fn first_i16(start: i16, end: i16) -> i16
//@ req true;
//@ ens if start < end { result == start } else { result == 77 };
//@ on_unwind_ens false;
{ let mut it = start..end; let r = &mut it; match r.next() { None => 77, Some(v) => v } }

unsafe fn first_i32(start: i32, end: i32) -> i32
//@ req true;
//@ ens if start < end { result == start } else { result == 77 };
//@ on_unwind_ens false;
{ let mut it = start..end; let r = &mut it; match r.next() { None => 77, Some(v) => v } }

unsafe fn first_i64(start: i64, end: i64) -> i64
//@ req true;
//@ ens if start < end { result == start } else { result == 77 };
//@ on_unwind_ens false;
{ let mut it = start..end; let r = &mut it; match r.next() { None => 77, Some(v) => v } }

unsafe fn first_i128(start: i128, end: i128) -> i128
//@ req true;
//@ ens if start < end { result == start } else { result == 77 };
//@ on_unwind_ens false;
{ let mut it = start..end; let r = &mut it; match r.next() { None => 77, Some(v) => v } }

unsafe fn first_isize(start: isize, end: isize) -> isize
//@ req true;
//@ ens if start < end { result == start } else { result == 77 };
//@ on_unwind_ens false;
{ let mut it = start..end; let r = &mut it; match r.next() { None => 77, Some(v) => v } }

fn main() {}
