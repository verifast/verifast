/*

Simple full functional specification & verification of "cat" (echos stdin to stdout) and "hi" (prints "hi", a simplified Hello world).

Represents an I/O specification using an approach inspired by coinduction.

*/

//@ #include "nat.gh"

/*@

inductive io_action = in(char) | out(char);

inductive iospec = iospec(fixpoint(pair<io_action, list<io_action> >, bool));

inductive result<t> =
| bad
| state(t)
| spec(iospec);

fixpoint iospec iospec_cons<t>(fixpoint(t, io_action, result<t>) stateMachine, t t0);

fixpoint option<iospec> iospec_apply(iospec s, io_action a);

lemma_auto(iospec_apply(((iospec_cons)(stateMachine))(t0), a)) void iospec_cons_apply_lemma<t>(fixpoint(t, io_action, result<t>) stateMachine, t t0, io_action a);
    requires true;
    ensures
        iospec_apply(((iospec_cons)(stateMachine))(t0), a) ==
        switch (stateMachine(t0, a)) {
            case bad: return none;
            case state(t1): return some(((iospec_cons)(stateMachine))(t1));
            case spec(s): return some(s);
        };

@*/

char getchar();
    //@ requires world(?s);
    //@ ensures world(?s1) &*& iospec_apply(s, in(result)) == some(s1);

void putchar(char c);
    //@ requires world(?s) &*& iospec_apply(s, out(c)) != none;
    //@ ensures world(the(iospec_apply(s, out(c))));

/*@

fixpoint result<list<char> > catSpec(list<char> buffer, io_action a) {
    switch (a) {
        case in(c): return state(append(buffer, cons(c, nil)));
        case out(c): return switch (buffer) {
            case nil: return bad;
            case cons(c0, buffer0): return c == c0 ? state(buffer0) : bad;
        };
    }
}

predicate world(iospec s);

@*/

void cat1()
    //@ requires world(((iospec_cons)(catSpec))(nil));
    //@ ensures world(((iospec_cons)(catSpec))(nil));
{
    for (;;)
        //@ invariant world(((iospec_cons)(catSpec))(nil));
    {
        char c = getchar();
        putchar(c);
    }
}

void cat2()
    //@ requires world(((iospec_cons)(catSpec))(nil));
    //@ ensures world(((iospec_cons)(catSpec))(nil));
{
    for (;;)
        //@ invariant world(((iospec_cons)(catSpec))(nil));
    {
        char c1 = getchar();
        char c2 = getchar();
        putchar(c1);
        putchar(c2);
    }
}

/*@

fixpoint result<unit> iospec_true_ctor(unit u, io_action a) {
    return state(u);
}

fixpoint iospec iospec_true() { return ((iospec_cons)(iospec_true_ctor))(unit); }

fixpoint result<list<io_action> > iospec_do_all(iospec cont, list<io_action> todo, io_action a) {
    return a == head(todo) ? tail(todo) == nil ? spec(cont) : state(tail(todo)) : bad;
}

@*/

void hi()
    //@ requires world((iospec_cons)((iospec_do_all)(iospec_true))(cons(out('h'), cons(out('i'), nil))));
    //@ ensures world(iospec_true);
{
    putchar('h');
    putchar('i');
}
