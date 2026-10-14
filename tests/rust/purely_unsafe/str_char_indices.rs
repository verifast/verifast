// verifast_options{ignore_ref_creation}
#![feature(likely_unlikely)]

// Tests for the specs of str::char_indices, CharIndices::next and hint::unlikely, and for the
// declaration of std::ops::RangeTo, in bin/rust/std/lib.rsspec.

// Iterating over "aé" with char_indices: (0, 'a'), (1, 'é'), then None. Then the iterator is dropped.
unsafe fn iterate(s: &str)
//@ req thread_token(?t) &*& [?f](s as *u8)[..s.len()] |-> [0x61, 0xC3, 0xA9];
//@ ens thread_token(t) &*& [f](s as *u8)[..s.len()] |-> [0x61, 0xC3, 0xA9];
//@ on_unwind_ens thread_token(t) &*& [f](s as *u8)[..s.len()] |-> [0x61, 0xC3, 0xA9];
{
    let mut chars = s.char_indices();
    let (i1, c1) = chars.next().unwrap_unchecked();
    //@ assert i1 == 0 &*& char_utf8(c1) == [0x61];
    //@ array_split(s as *u8, 1);
    let (i2, c2) = chars.next().unwrap_unchecked();
    //@ assert i2 == 1 &*& char_utf8(c2) == [0xC3, 0xA9];
    //@ array_split(s as *u8 + 1, 2);
    let r = chars.next();
    //@ assert r == std::option::Option::None;
    //@ array_join(s as *u8 + 1);
    //@ array_join(s as *u8);
    std::mem::drop(chars);
}

// The index of a char is the number of bytes before it: in "💣a", 'a' is at index 4.
unsafe fn index_after_four_byte_char(s: &str) -> usize
//@ req thread_token(?t) &*& [?f](s as *u8)[..s.len()] |-> [0xF0, 0x9F, 0x92, 0xA3, 0x61];
//@ ens thread_token(t) &*& [f](s as *u8)[..s.len()] |-> [0xF0, 0x9F, 0x92, 0xA3, 0x61] &*& result == 4;
//@ on_unwind_ens thread_token(t) &*& [f](s as *u8)[..s.len()] |-> [0xF0, 0x9F, 0x92, 0xA3, 0x61];
{
    let mut chars = s.char_indices();
    let (i1, c1) = chars.next().unwrap_unchecked();
    //@ assert i1 == 0 &*& char_len_utf8(c1) == 4;
    //@ array_split(s as *u8, 4);
    let (i2, c2) = chars.next().unwrap_unchecked();
    //@ assert char_utf8(c2) == [0x61];
    //@ array_join(s as *u8);
    std::mem::drop(chars);
    i2
}

// The fast path of String::retain: stop at the first char that the condition rejects (here: a char
// that is not ASCII) and return its index.
unsafe fn first_non_ascii(s: &str) -> usize
//@ req thread_token(?t) &*& [?f](s as *u8)[..s.len()] |-> [0x61, 0xC3, 0xA9];
//@ ens thread_token(t) &*& [f](s as *u8)[..s.len()] |-> [0x61, 0xC3, 0xA9] &*& result == 1;
//@ on_unwind_ens thread_token(t) &*& [f](s as *u8)[..s.len()] |-> [0x61, 0xC3, 0xA9];
{
    let mut chars = s.char_indices();
    let (i1, c1) = chars.next().unwrap_unchecked();
    //@ array_split(s as *u8, 1);
    let r = if std::hint::unlikely(c1.len_utf8() != 1) {
        i1
    } else {
        let (i2, c2) = chars.next().unwrap_unchecked();
        if std::hint::unlikely(c2.len_utf8() != 1) { i2 } else { s.len() }
    };
    //@ array_join(s as *u8);
    std::mem::drop(chars);
    r
}

fn unlikely_test() {
    let b1 = std::hint::unlikely(true);
    //@ assert b1 == true;
    let b2 = std::hint::unlikely(false);
    //@ assert b2 == false;
}

fn range_to_test(n: usize) {
    let r = ..n;
    let e = r.end;
    //@ assert e == n;
}

// Negative tests

// CharIndices::next requires the remaining bytes to be valid UTF-8 (here, a lone continuation byte).
unsafe fn next_on_invalid(chars: &mut std::str::CharIndices<'static>)
//@ req *chars |-> ?chars0 &*& <std::str::CharIndices<'static>>.own(?t, chars0) &*& [?f](chars0.as_str() as *u8)[..chars0.as_str().len()] |-> [0xA9];
//@ ens true;
{
    chars.next(); //~should_fail
}

// CharIndices::next needs (read access to) the bytes it decodes.
unsafe fn next_no_permission(s: &str)
//@ req thread_token(?t);
//@ ens thread_token(t);
{
    let mut chars = s.char_indices();
    chars.next(); //~should_fail
}

// There is no second char in "a".
unsafe fn next_past_end(s: &str)
//@ req thread_token(?t) &*& [?f](s as *u8)[..s.len()] |-> [0x61];
//@ ens thread_token(t) &*& [f](s as *u8)[..s.len()] |-> [0x61];
{
    let mut chars = s.char_indices();
    chars.next().unwrap_unchecked();
    //@ array_split(s as *u8, 1);
    chars.next().unwrap_unchecked(); //~should_fail
}

// In "aé", 'é' is at index 1, not 2.
unsafe fn wrong_index(s: &str)
//@ req thread_token(?t) &*& [?f](s as *u8)[..s.len()] |-> [0x61, 0xC3, 0xA9];
//@ ens thread_token(t) &*& [f](s as *u8)[..s.len()] |-> [0x61, 0xC3, 0xA9];
{
    let mut chars = s.char_indices();
    chars.next().unwrap_unchecked();
    //@ array_split(s as *u8, 1);
    let (i2, c2) = chars.next().unwrap_unchecked();
    //@ assert i2 == 2; //~should_fail
}

// Dropping a CharIndices requires <CharIndices>.own, which this function does not have.
unsafe fn drop_without_own(chars: std::str::CharIndices<'static>)
//@ req thread_token(?t);
//@ ens thread_token(t);
{
    std::mem::drop(chars); //~should_fail
}

fn unlikely_wrong() {
    let b = std::hint::unlikely(true);
    //@ assert b == false; //~should_fail
}

fn main() {}
