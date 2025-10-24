//@ use std::str::str;

//@ pred small_str(s: *str) = str(s, _) &*& s.len <= 20;
//@ pred large_str(s: *str) = str(s, _) &*& s.len <= 1000;

unsafe fn read_lines() -> *const *const str
//@ req true;
//@ ens result[..100] |-> ?lines &*& foreach(lines, small_str);
{
    std::process::abort(); // TODO: Implement
}

unsafe fn write_lines(p: *const *const str)
//@ req p[..100] |-> ?lines &*& foreach(lines, large_str);
//@ ens true;
{
    std::process::abort(); // TODO: Implement
}

/*@

lem_type conversion_lemma<t>(P: pred(t), Q: pred(t)) = lem();
    req P(?x);
    ens Q(x);

lem convert_foreach<t>()
    req foreach::<t>(?xs, ?P) &*& is_conversion_lemma(?convert, P, ?Q);
    ens foreach::<t>(xs, Q) &*& is_conversion_lemma(convert, P, Q);
{
    open foreach(xs, P);
    match xs {
        nil => {}
        cons(x0, xs0) => {
            convert();
            convert_foreach();
        }
    }
    close foreach(xs, Q);
}

lem foreach_small_large_string()
    req foreach(?strings, small_str);
    ens foreach(strings, large_str);
{
    produce_lem_ptr_chunk conversion_lemma<*str>(small_str, large_str)() {
        open small_str(?s);
        close large_str(s);
    } {
        convert_foreach();
    }
}

@*/

fn main()
//@ req true;
//@ ens true;
{
    unsafe {
        let p = read_lines();
        //@ foreach_small_large_string();
        write_lines(p);
    }
}
