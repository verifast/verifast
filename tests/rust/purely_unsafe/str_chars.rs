// verifast_options{ignore_ref_creation}

// Tests for the specs of str::get_unchecked, str::chars, Chars::next, char::len_utf8,
// char::encode_utf8, slice::from_raw_parts_mut, str::from_utf8_unchecked and
// str::from_utf8_unchecked_mut in bin/rust/std/lib.rsspec.

// The suffix of a string slice that starts at a char boundary.
unsafe fn suffix<'a>(s: &'a str, i: usize) -> &'a str
//@ req [?f](s as *u8)[..s.len()] |-> ?bs &*& i <= s.len() &*& is_char_boundary(bs, i) == true;
//@ ens [f](s as *u8)[..s.len()] |-> bs &*& result as *u8 == s as *u8 + i &*& result.len() == s.len() - i;
{
    let r = s.get_unchecked(i..s.len());
    //@ take_length(drop(i, bs));
    //@ array_join(s as *u8);
    //@ array_join(s as *u8);
    r
}

// The first char of a non-empty string slice: its UTF-8 encoding is a prefix of the bytes.
unsafe fn first_char(s: &str) -> char
//@ req [?f](s as *u8)[..s.len()] |-> ?bs &*& is_valid_utf8(bs) == true &*& bs != [];
/*@
ens [f](s as *u8)[..s.len()] |-> bs &*&
    char_len_utf8(result) == utf8_seq_len(head(bs)) &*&
    char_utf8(result) == take(char_len_utf8(result), bs) &*&
    is_unicode_scalar_value(result) == true;
@*/
{
    s.chars().next().unwrap_unchecked()
}

// The expression from String::retain: decode the char at byte index i.
unsafe fn char_at(s: &str, i: usize) -> char
/*@
req [?f](s as *u8)[..s.len()] |-> ?bs &*& i < s.len() &*& is_char_boundary(bs, i) == true &*&
    is_valid_utf8(drop(i, bs)) == true;
@*/
//@ ens [f](s as *u8)[..s.len()] |-> bs &*& char_utf8(result) == take(char_len_utf8(result), drop(i, bs));
{
    //@ take_length(drop(i, bs));
    let c = s.get_unchecked(i..s.len()).chars().next().unwrap_unchecked();
    //@ array_join(s as *u8);
    //@ array_join(s as *u8);
    c
}

// Iterating over all chars of "aé": Some('a'), Some('é'), then None.
unsafe fn iterate(s: &str)
//@ req [?f](s as *u8)[..s.len()] |-> [0x61, 0xC3, 0xA9];
//@ ens [f](s as *u8)[..s.len()] |-> [0x61, 0xC3, 0xA9];
{
    let mut chars = s.chars();
    let c1 = chars.next().unwrap_unchecked();
    //@ assert char_utf8(c1) == [0x61];
    //@ array_split(s as *u8, 1);
    let c2 = chars.next().unwrap_unchecked();
    //@ assert char_utf8(c2) == [0xC3, 0xA9];
    //@ array_split(s as *u8 + 1, 2);
    let c3 = chars.next();
    //@ assert c3 == std::option::Option::None;
    //@ array_join(s as *u8 + 1);
    //@ array_join(s as *u8);
}

fn len_utf8_test() {
    let n1 = 'a'.len_utf8();
    //@ assert n1 == 1;
    let n2 = 'ß'.len_utf8();
    //@ assert n2 == 2;
    let n3 = 'ℝ'.len_utf8();
    //@ assert n3 == 3;
    let n4 = '💣'.len_utf8();
    //@ assert n4 == 4;
}

// Encoding a char into a 4-byte buffer writes char_len_utf8(c) bytes, which are valid UTF-8.
unsafe fn encode_into(c: char, p: *mut u8) -> usize
//@ req p[..4] |-> ?bs0 &*& p != 0;
/*@
ens p[..char_len_utf8(c)] |-> char_utf8(c) &*& (p + char_len_utf8(c))[..4 - char_len_utf8(c)] |-> drop(char_len_utf8(c), bs0) &*&
    result == char_len_utf8(c) &*& if is_unicode_scalar_value(c) { is_valid_utf8(char_utf8(c)) == true } else { true };
@*/
{
    //@ div_rem_nonneg(p as usize, 1);
    let s = c.encode_utf8(std::slice::from_raw_parts_mut(p, 4));
    s.len()
}

// Decoding the first char of a string and encoding it into a buffer copies the first char's bytes.
unsafe fn copy_first_char(s: &str, p: *mut u8)
//@ req [?f](s as *u8)[..s.len()] |-> ?bs &*& is_valid_utf8(bs) == true &*& bs != [] &*& p[..4] |-> ?bs0 &*& p != 0;
//@ ens [f](s as *u8)[..s.len()] |-> bs &*& p[..utf8_seq_len(head(bs))] |-> take(utf8_seq_len(head(bs)), bs) &*& (p + utf8_seq_len(head(bs)))[..4 - utf8_seq_len(head(bs))] |-> drop(utf8_seq_len(head(bs)), bs0);
{
    let c = s.chars().next().unwrap_unchecked();
    let n = c.len_utf8();
    //@ array_split(p, n);
    //@ div_rem_nonneg(p as usize, 1);
    c.encode_utf8(std::slice::from_raw_parts_mut(p, n));
}

unsafe fn str_from_bytes<'a>(v: &'a [u8]) -> &'a str
//@ req [?f](v as *u8)[..v.len()] |-> ?bs &*& is_valid_utf8(bs) == true;
//@ ens [f](v as *u8)[..v.len()] |-> bs &*& result as *u8 == v as *u8 &*& result.len() == v.len();
{
    std::str::from_utf8_unchecked(v)
}

unsafe fn str_from_bytes_mut<'a>(v: &'a mut [u8]) -> &'a mut str
//@ req (v as *u8)[..v.len()] |-> ?bs &*& is_valid_utf8(bs) == true;
//@ ens (v as *u8)[..v.len()] |-> bs &*& result as *u8 == v as *u8 &*& result.len() == v.len();
{
    std::str::from_utf8_unchecked_mut(v)
}

// Decoding "ℝ" ([0xE2, 0x84, 0x9D]) gives a 3-byte char.
unsafe fn decode_three_bytes(s: &str) -> usize
//@ req [?f](s as *u8)[..s.len()] |-> [0xE2, 0x84, 0x9D];
//@ ens [f](s as *u8)[..s.len()] |-> [0xE2, 0x84, 0x9D] &*& result == 3;
{
    let c = s.chars().next().unwrap_unchecked();
    c.len_utf8()
}

// A 4-byte sequence: '💣' (U+1F4A3) is [0xF0, 0x9F, 0x92, 0xA3].
unsafe fn decode_four_bytes(s: &str) -> usize
//@ req [?f](s as *u8)[..s.len()] |-> [0xF0, 0x9F, 0x92, 0xA3];
//@ ens [f](s as *u8)[..s.len()] |-> [0xF0, 0x9F, 0x92, 0xA3] &*& result == 4;
{
    let c = s.chars().next().unwrap_unchecked();
    c.len_utf8()
}

// U+D7FF ([0xED, 0x9F, 0xBF]), the last scalar value before the surrogates: decoding it and encoding it
// again gives valid UTF-8.
unsafe fn round_trip_d7ff(s: &str, p: *mut u8)
//@ req [?f](s as *u8)[..s.len()] |-> [0xED, 0x9F, 0xBF] &*& p[..4] |-> ?bs0 &*& p != 0;
//@ ens [f](s as *u8)[..s.len()] |-> [0xED, 0x9F, 0xBF] &*& p[..3] |-> [0xED, 0x9F, 0xBF] &*& (p + 3)[..1] |-> drop(3, bs0);
{
    let c = s.chars().next().unwrap_unchecked();
    //@ div_rem_nonneg(p as usize, 1);
    let r = c.encode_utf8(std::slice::from_raw_parts_mut(p, 4));
    //@ assert is_valid_utf8(char_utf8(c)) == true;
}

// A decoded char satisfies char_own, which is what calling a closure `F: FnMut(char)` requires.
unsafe fn decoded_char_own(s: &str) -> char
//@ req [?f](s as *u8)[..s.len()] |-> ?bs &*& is_valid_utf8(bs) == true &*& bs != [];
//@ ens [f](s as *u8)[..s.len()] |-> bs &*& char_own(currentThread, result);
{
    let c = s.chars().next().unwrap_unchecked();
    //@ close char_own(currentThread, c);
    c
}

// Negative tests. Each failing call is the first call in its function: a failure after an earlier
// call leaves call context behind, which would hide the locations of later expected failures.

// get_unchecked: the range must be in bounds, start <= end, and both ends on char boundaries.
unsafe fn get_unchecked_out_of_bounds(s: &str)
//@ req [?f](s as *u8)[..s.len()] |-> ?bs;
//@ ens [f](s as *u8)[..s.len()] |-> bs;
{
    s.get_unchecked(0..s.len() + 1); //~should_fail
}

unsafe fn get_unchecked_start_after_end(s: &str)
//@ req [?f](s as *u8)[..s.len()] |-> ?bs &*& s.len() == 2;
//@ ens [f](s as *u8)[..s.len()] |-> bs;
{
    s.get_unchecked(2..1); //~should_fail
}

// "é" is [0xC3, 0xA9]; byte index 1 is not a char boundary.
unsafe fn get_unchecked_off_boundary(s: &str)
//@ req [?f](s as *u8)[..s.len()] |-> [0xC3, 0xA9];
//@ ens [f](s as *u8)[..s.len()] |-> [0xC3, 0xA9];
{
    s.get_unchecked(1..2); //~should_fail
}

// The end index must be on a char boundary too.
unsafe fn get_unchecked_end_off_boundary(s: &str)
//@ req [?f](s as *u8)[..s.len()] |-> [0xC3, 0xA9];
//@ ens [f](s as *u8)[..s.len()] |-> [0xC3, 0xA9];
{
    s.get_unchecked(0..1); //~should_fail
}

// get_unchecked needs (read access to) the bytes of the string slice.
unsafe fn get_unchecked_no_permission(s: &str)
//@ req true;
//@ ens true;
{
    s.get_unchecked(0..0); //~should_fail
}

// Chars::next requires the remaining bytes to be valid UTF-8 (here, a lone continuation byte).
unsafe fn next_on_invalid(chars: &mut std::str::Chars<'static>) -> std::option::Option<char>
//@ req *chars |-> ?chars0 &*& [?f](chars0.as_str() as *u8)[..chars0.as_str().len()] |-> [0xA9];
//@ ens true;
{
    chars.next() //~should_fail
}

// encode_utf8 requires a buffer that is large enough: 'ß' needs 2 bytes.
unsafe fn encode_too_small(dst: &mut [u8])
//@ req (dst as *u8)[..dst.len()] |-> ?bs0 &*& dst.len() == 1;
//@ ens (dst as *u8)[..dst.len()] |-> _;
{
    'ß'.encode_utf8(dst); //~should_fail
}

// from_raw_parts_mut requires initialized memory.
unsafe fn from_raw_parts_mut_uninit(p: *mut u8)
//@ req p[..4] |-> _ &*& p != 0;
//@ ens p[..4] |-> _;
{
    std::slice::from_raw_parts_mut(p, 4); //~should_fail
}

// from_raw_parts_mut requires a non-null pointer, even for an empty slice.
unsafe fn from_raw_parts_mut_null(p: *mut u8)
//@ req p == 0;
//@ ens true;
{
    std::slice::from_raw_parts_mut(p, 0); //~should_fail
}

// from_utf8_unchecked requires valid UTF-8.
unsafe fn from_utf8_unchecked_invalid<'a>(v: &'a [u8]) -> &'a str
//@ req [?f](v as *u8)[..v.len()] |-> [0xC3];
//@ ens [f](v as *u8)[..v.len()] |-> [0xC3];
{
    std::str::from_utf8_unchecked(v) //~should_fail
}

// A surrogate (U+D800) is not valid UTF-8.
unsafe fn from_utf8_unchecked_mut_invalid<'a>(v: &'a mut [u8]) -> &'a mut str
//@ req (v as *u8)[..v.len()] |-> [0xED, 0xA0, 0x80];
//@ ens (v as *u8)[..v.len()] |-> [0xED, 0xA0, 0x80];
{
    std::str::from_utf8_unchecked_mut(v) //~should_fail
}

// Checked last (the failing call is not the first call): Chars::next on an empty string returns None,
// which cannot be unwrapped.
unsafe fn next_on_empty(s: &str) -> char
//@ req [?f](s as *u8)[..s.len()] |-> [];
//@ ens [f](s as *u8)[..s.len()] |-> [];
{
    s.chars().next().unwrap_unchecked() //~should_fail
}

fn main() {}
