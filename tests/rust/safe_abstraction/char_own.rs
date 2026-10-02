// `<char>.own` and `<char>.full_borrow_content` are `char_own` and `char_full_borrow_content`, as for the other
// primitive types, and 1-tuples have open/close lemmas for their ownership, as 0-tuples and 4-tuples do.

/*@

lem char_own_is_char_own(t: thread_id_t, c: char)
    req char_own(t, c);
    ens <char>.own(t, c);
{
}

lem char_fbc_is_char_fbc(t: thread_id_t, l: *char)
    req char_full_borrow_content(t, l)();
    ens (<char>.full_borrow_content(t, l))();
{
}

lem char_own_valid(t: thread_id_t, c: char)
    req <char>.own(t, c);
    ens <char>.own(t, c) &*& c as u32 <= 0x10FFFF &*& !(0xD800 <= c as u32 && c as u32 <= 0xDFFF);
{
    open char_own(t, c);
}

lem char_tuple_valid(t: thread_id_t, v: (char,))
    req <(char,)>.own(t, v);
    ens <(char,)>.own(t, v) &*& v.0 as u32 <= 0x10FFFF;
{
    open_tuple_1_own(t, v);
    open char_own(t, v.0);
    close char_own(t, v.0);
    close_tuple_1_own(t, v);
}

// The tuple lemmas exchange the tuple's ownership for the element's; they do not duplicate it.
lem tuple_1_own_not_duplicable<T1>(t: thread_id_t, v: (T1,))
    req <(T1,)>.own(t, v);
    ens <(T1,)>.own(t, v) &*& <T1>.own(t, v.0); //~should_fail
{
    open_tuple_1_own(t, v);
    close_tuple_1_own(t, v);
}

// `<char>.own` holds for a valid char, but not for a surrogate code point: unlike `<bool>.own`, it is not
// trivially true.
lem char_own_valid_char(t: thread_id_t)
    req true;
    ens <char>.own(t, 'x');
{
}

lem char_own_surrogate(t: thread_id_t)
    req true;
    ens <char>.own(t, 0xD800 as char); //~should_fail
{
}

@*/

fn identity<T>(x: T) -> T {
    x
}

// A char passed to and returned from a generic function.
fn char_identity(c: char) -> char {
    identity(c)
}

// Calling a closure with a char argument requires `<(char,)>.own(t, (c,))` (see the spec of `FnMut::call_mut`).
fn call_with_char<F: FnMut(char) -> bool>(mut f: F) -> bool {
    let c = 'x';
    //@ close char_own(_t, c);
    //@ close_tuple_1_own::<char>(_t, std_tuple_1_::<char> { 0: c });
    f(c)
}

fn main() {}
