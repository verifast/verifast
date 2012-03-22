/*

Simple full functional specification & verification of "cat" (echos stdin to stdout) and "hi" (prints "hi", a simplified Hello world).

Represents an I/O specification using an approach inspired by coinduction.

*/

//@ #include "nat.h"

/*@

inductive option<t> = none | some(t);

fixpoint t the<t>(option<t> o) {
    switch (o) {
        case none: return default_value;
        case some(v): return v;
    }
}

@*/

/*@

inductive io_action = in(char) | out(char);

inductive iospec = iospec(fixpoint(fixpoint(nat, io_action), bool));

fixpoint fixpoint(t, iospec) iospec_cons<t>(fixpoint(fixpoint(t, iospec), t, io_action, option<iospec>) body);

fixpoint option<iospec> iospec_apply(iospec s, io_action a);

lemma_auto(iospec_apply((iospec_cons(body))(t0), a)) void iospec_cons_apply_lemma<t>(fixpoint(fixpoint(t, iospec), t, io_action, option<iospec>) body, t t0, io_action a);
    requires true;
    ensures iospec_apply((iospec_cons(body))(t0), a) == body(iospec_cons(body), t0, a);

@*/

char getchar();
    //@ requires world(?s);
    //@ ensures world(?s1) &*& iospec_apply(s, in(result)) == some(s1);

void putchar(char c);
    //@ requires world(?s) &*& iospec_apply(s, out(c)) != none;
    //@ ensures world(the(iospec_apply(s, out(c))));

/*@

fixpoint option<iospec> catSpec(fixpoint(list<char>, iospec) rec, list<char> buffer, io_action a) {
    switch (a) {
        case in(c): return some(rec(append(buffer, cons(c, nil))));
        case out(c): return switch (buffer) {
            case nil: return none;
            case cons(c0, buffer0): return c == c0 ? some(rec(buffer0)) : none;
        };
    }
}

predicate world(iospec s);

@*/

void cat1()
    //@ requires world((iospec_cons(catSpec))(nil));
    //@ ensures world((iospec_cons(catSpec))(nil));
{
    for (;;)
        //@ invariant world((iospec_cons(catSpec))(nil));
    {
        char c = getchar();
        putchar(c);
    }
}

void cat2()
    //@ requires world((iospec_cons(catSpec))(nil));
    //@ ensures world((iospec_cons(catSpec))(nil));
{
    for (;;)
        //@ invariant world((iospec_cons(catSpec))(nil));
    {
        char c1 = getchar();
        char c2 = getchar();
        putchar(c1);
        putchar(c2);
    }
}

/*@

fixpoint option<iospec> iospec_true_ctor(fixpoint(unit, iospec) rec, unit u, io_action a) {
    return some(rec(u));
}

fixpoint iospec iospec_true() { return (iospec_cons)(iospec_true_ctor)(unit); }

fixpoint option<iospec> iospec_do_all(iospec cont, fixpoint(list<io_action>, iospec) rec, list<io_action> todo, io_action a) {
    return a == head(todo) ? some(tail(todo) == nil ? cont : rec(tail(todo))) : none;
}

@*/

void hi()
    //@ requires world((iospec_cons)((iospec_do_all)(iospec_true))(cons(out('h'), cons(out('i'), nil))));
    //@ ensures world(iospec_true);
{
    putchar('h');
    putchar('i');
}
