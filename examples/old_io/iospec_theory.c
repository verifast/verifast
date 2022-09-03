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

fixpoint bool has_trace(fixpoint(pair<io_action, list<io_action> >, bool) traces, list<io_action> trace) {
    switch (trace) {
        case nil: return true;
        case cons(a, trace0): return traces(pair(a, trace0));
    }
}

fixpoint bool has_ptrace(fixpoint(list<io_action>, bool) traces, pair<io_action, list<io_action> > trace) {
    switch (trace) {
        case pair(a, trace0): return traces(cons(a, trace0));
    }
}

fixpoint bool check_trace<t>(fixpoint(t, io_action, result<t>) stateMachine, t t0, list<io_action> trace) {
    switch (trace) {
        case nil: return true;
        case cons(a, trace0): return
            switch (stateMachine(t0, a)) {
                case bad: return false;
                case state(t1): return check_trace(stateMachine, t1, trace0);
                case spec(s): return switch (s) { case iospec(traces): return has_trace(traces, trace0); };
            };
    }
}

fixpoint iospec iospec_cons<t>(fixpoint(t, io_action, result<t>) stateMachine, t t0) {
    return iospec((has_ptrace)((check_trace)(stateMachine, t0)));
}

fixpoint bool check_prefixed_trace(fixpoint(pair<io_action, list<io_action> >, bool) traces, io_action a, list<io_action> trace) {
    return traces(pair(a, trace));
}

fixpoint option<iospec> iospec_apply(iospec s, io_action a) {
    switch (s) {
        case iospec(traces): return
            traces(pair(a, nil)) ?
                some(iospec((has_ptrace)((check_prefixed_trace)(traces, a))))
            :
                none;
    }
}

typedef lemma void fun_eq_at<a, b>(fixpoint(a, b) f1, fixpoint(a, b) f2)(a x);
    requires true;
    ensures f1(x) == f2(x);

lemma void fun_ext<a, b>();
    requires is_fun_eq_at<a, b>(?lem, ?f1, ?f2);
    ensures is_fun_eq_at(lem, f1, f2) &*& f1 == f2;

lemma_auto(iospec_apply(((iospec_cons)(stateMachine))(t0), a)) void iospec_cons_apply_lemma<t>(fixpoint(t, io_action, result<t>) stateMachine, t t0, io_action a)
    requires true;
    ensures
        iospec_apply(((iospec_cons)(stateMachine))(t0), a) ==
        switch (stateMachine(t0, a)) {
            case bad: return none;
            case state(t1): return some(((iospec_cons)(stateMachine))(t1));
            case spec(s): return some(s);
        };
{
    switch (stateMachine(t0, a)) {
        case bad:
            ;
        case state(t1):
            {
                lemma void aux(pair<io_action, list<io_action> > trace)
                    requires true;
                    ensures true;
                {
                }
                produce_lemma_function_pointer_chunk(aux) :
                    fun_eq_at<pair<io_action, list<io_action> >, bool>(
                        (has_ptrace)((check_prefixed_trace)((has_ptrace)((check_trace)(stateMachine, t0)), a)),
                        (has_ptrace)((check_trace)(stateMachine, t1)))(trace)
                {
                    call();
                    switch (trace) {
                        case pair(a0, trace0):
                    }
                }
                {
                    fun_ext();
                }
            }
            ;
        case spec(s):
            switch (s) {
                case iospec(traces):
                    {
                        lemma void aux(pair<io_action, list<io_action> > trace)
                            requires true;
                            ensures true;
                        {
                        }
                        produce_lemma_function_pointer_chunk(aux) :
                            fun_eq_at<pair<io_action, list<io_action> >, bool>(
                                (has_ptrace)((check_prefixed_trace)((has_ptrace)((check_trace)(stateMachine, t0)), a)),
                                traces
                            )(trace)
                        {
                            call();
                            switch (trace) {
                                case pair(a0, trace0):
                            }
                        }
                        {
                            fun_ext();
                        }
                    }
                    ;
            }
    }
}

@*/

