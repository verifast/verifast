/*

Worlds
======

A world represents (part of) the environment, with which the program can interact by performing I/O actions.
An input action is an action initiated by the environment and observed by the program;
an output action is an action initiated by the program and observed by the environment.
A world specifies a constraint on both the program and the environment, in the form of a state machine. The
state machine has an action space, a state space, an id, an is_out function, a current state, an allowed function, and a next function.
A world may be a projection of a larger world; the id identifies the projection.
The is_out function specifies which actions are output actions; the other actions are input actions.
The allowed function specifies whether a given action is allowed in a given state; the next function
specifies the next state when a given action is performed in a given state. That is, the state machine specified
by a world is deterministic. (A deterministic state machine M' can be derived from any non-deterministic one M by using as state space for M' the powerset of
the state space of M.)

*/

/*@

predicate world<a, s>(int id, fixpoint(a, bool) is_out, s state, fixpoint(s, a, bool) allowed, fixpoint(s, a, s) next);

@*/

/*

World transformations
=====================

The following transformations are possible on worlds:
- State space projection. This replaces the world by another world that is stricter for the program and more lenient for the environment. To verify this,
  a special kind of simulation relation must be provided, that takes into account whether an action is an input action or an output action.
- Splitting. A world that is a parallel composition of two worlds with disjoint action spaces, can be split up into its component worlds.

*/

// State space projection

/*@

typedef lemma void is_sim<a, s1, s2>(
        fixpoint(a, bool) is_out,
        fixpoint(s1, a, bool) allowed1, fixpoint(s1, a, s1) next1,
        fixpoint(s2, a, bool) allowed2, fixpoint(s2, a, s2) next2,
        fixpoint(s1, s2, bool) sim
    )(s1 s1, s2 s2, a a);
    requires sim(s1, s2) == true &*& is_out(a) ? allowed2(s2, a) == true : allowed1(s1, a) == true;
    ensures allowed1(s1, a) == true &*& allowed2(s2, a) == true &*& sim(next1(s1, a), next2(s2, a)) == true;

predicate unproject_token<a, s1, s2>(int id_new, int id_old, fixpoint(s1, a, bool) allowed, fixpoint(s1, a, s1) next, fixpoint(s1, s2, bool) sim);

lemma int project_world<a, s1, s2>(fixpoint(s2, a, bool) allowed2, fixpoint(s2, a, s2) next2, fixpoint(s1, s2, bool) sim, is_sim *is_sim, s2 s_new);
    requires
        world<a, s1>(?id_old, ?is_out, ?s_old, ?allowed1, ?next1) &*&
        is_is_sim<a, s1, s2>(is_sim, is_out, allowed1, next1, allowed2, next2, sim) &*&
        sim(s_old, s_new) == true;
    ensures
        world<a, s2>(result, is_out, s_new, allowed2, next2) &*&
        is_is_sim<a, s1, s2>(is_sim, is_out, allowed1, next1, allowed2, next2, sim) &*&
        unproject_token<a, s1, s2>(result, id_old, allowed1, next1, sim);

lemma void unproject_world<a, s1, s2>();
    requires world<a, s2>(?id_new, ?is_out, ?s_new, ?allowed2, ?next2) &*& unproject_token<a, s1, s2>(id_new, ?id_old, ?allowed1, ?next1, ?sim);
    ensures world<a, s1>(id_old, is_out, ?s_old, allowed1, next1) &*& sim(s_old, s_new) == true;

@*/

// Splitting

/*@

inductive sum<a, b> = left(a) | right(b);

fixpoint c lift_sum<a, b, c>(fixpoint(a, c) f1, fixpoint(b, c) f2, sum<a, b> x) {
    switch (x) {
        case left(a): return f1(a);
        case right(b): return f2(b);
    }
}

fixpoint bool lift_allowed<a1, a2, s1, s2>(fixpoint(s1, a1, bool) allowed1, fixpoint(s2, a2, bool) allowed2, pair<s1, s2> s, sum<a1, a2> a) {
    switch (a) {
        case left(a1): return allowed1(fst(s), a1);
        case right(a2): return allowed2(snd(s), a2);
    }
}

fixpoint pair<s1, s2> lift_next<a1, a2, s1, s2>(fixpoint(s1, a1, s1) next1, fixpoint(s2, a2, s2) next2, pair<s1, s2> s, sum<a1, a2> a) {
    switch (a) {
        case left(a1): return pair(next1(fst(s), a1), snd(s));
        case right(a2): return pair(fst(s), next2(snd(s), a2));
    }
}

predicate action_spaces_disjoint<a1, a2>();

lemma int split_world<a1, a2, s1, s2>(
        fixpoint(a1, bool) is_out1, s1 s1, fixpoint(s1, a1, bool) allowed1, fixpoint(s1, a1, s1) next1,
        fixpoint(a2, bool) is_out2, s2 s2, fixpoint(s2, a2, bool) allowed2, fixpoint(s2, a2, s2) next2);
    requires world<sum<a1, a2>, pair<s1, s2> >(?id, (lift_sum)(is_out1, is_out2), pair(s1, s2), (lift_allowed)(allowed1, allowed2), (lift_next)(next1, next2));
    ensures world<a1, s1>(id, is_out1, s1, allowed1, next1) &*& world<a2, s2>(id, is_out2, s2, allowed2, next2) &*& [_]action_spaces_disjoint<a1, a2>();

lemma void unsplit_world<a1, a2, s1, s2>();
    requires [_]action_spaces_disjoint<a1, a2>() &*& world<a1, s1>(?id, ?is_out1, ?s1, ?allowed1, ?next1) &*& world<a2, s2>(id, ?is_out2, ?s2, ?allowed2, ?next2);
    ensures world<sum<a1, a2>, pair<s1, s2> >(id, (lift_sum)(is_out1, is_out2), pair(s1, s2), (lift_allowed)(allowed1, allowed2), (lift_next)(next1, next2));

@*/

// getchar

/*@

inductive getchar_action = getchar_action | getchar_return_action(int);

fixpoint bool getchar_action_is_out(getchar_action a) {
    switch (a) {
        case getchar_action: return true;
        case getchar_return_action(result): return false;
    }
}

@*/

int getchar/*@ <s> @*/();
    //@ requires world<getchar_action, s>(?id, getchar_action_is_out, ?s, ?allowed, ?next) &*& allowed(s, getchar_action) == true;
    /*@
    ensures
        allowed(next(s, getchar_action), getchar_return_action(result)) == true &*&
        world<getchar_action, s>(id, getchar_action_is_out, next(next(s, getchar_action), getchar_return_action(result)), allowed, next);
    @*/

// putchar

/*@

inductive putchar_action = putchar_action(char) | putchar_return_action;

fixpoint bool putchar_action_is_out(putchar_action a) {
    switch (a) {
        case putchar_action(c): return true;
        case putchar_return_action: return false;
    }
}

@*/

void putchar/*@ <s> @*/(char c);
    //@ requires world<putchar_action, s>(?id, putchar_action_is_out, ?s, ?allowed, ?next) &*& allowed(s, putchar_action(c)) == true;
    /*@
    ensures
        allowed(next(s, putchar_action(c)), putchar_return_action) == true &*&
        world<putchar_action, s>(id, putchar_action_is_out, next(next(s, putchar_action(c)), putchar_return_action), allowed, next);
    @*/

/*

Example: cat.

This example illustrates how a function that uses both getchar and putchar can be verified, even though
getchar is specified in terms of an action space getchar_action, and putchar is specified in terms of an
action space putchar_action.

*/

/*@

fixpoint bool is_suffix_of<t>(list<t> xs, list<t> ys) {
    switch (ys) {
        case nil: return xs == ys;
        case cons(y, ys0): return xs == ys || is_suffix_of(xs, ys0);
    }
}

lemma void is_suffix_of_trans<t>(list<t> xs, list<t> ys, list<t> zs)
    requires is_suffix_of(xs, ys) == true &*& is_suffix_of(ys, zs) == true;
    ensures is_suffix_of(xs, zs) == true;
{
    switch (zs) {
        case nil:
        case cons(z, zs0):
            if (ys == zs) {
            } else {
                is_suffix_of_trans(xs, ys, zs0);
            }
    }
}

lemma void is_suffix_of_refl<t>(list<t> xs)
    requires true;
    ensures is_suffix_of(xs, xs) == true;
{
    switch (xs) {
        case nil:
        case cons(x, xs0):
    }
}

// catstate: read and written are the reverse of the sequence of characters read and written by the program.

inductive catstate = catstate(bool eof, list<char> read, list<char> written);

fixpoint bool cat_allowed(catstate s, sum<getchar_action, putchar_action> a) {
    switch (s) {
        case catstate(eof, read, written): return
            switch (a) {
                case left(ag): return
                    switch (ag) {
                        case getchar_action: return !eof;
                        case getchar_return_action(result): return true;
                    };
                case right(ap): return
                    switch (ap) {
                        case putchar_action(c): return is_suffix_of(cons(c, written), read);
                        case putchar_return_action: return true;
                    };
            };
    }
}

fixpoint catstate cat_next(catstate s, sum<getchar_action, putchar_action> a) {
    switch (s) {
        case catstate(eof, read, written): return
            switch (a) {
                case left(ag): return
                    switch (ag) {
                        case getchar_action: return s;
                        case getchar_return_action(result): return 0 <= result ? catstate(eof, cons((char)result, read), written) : catstate(true, read, written);
                    };
                case right(ap): return
                    switch (ap) {
                        case putchar_action(c): return catstate(eof, read, cons(c, written));
                        case putchar_return_action: return s;
                    };
            };
    }
}

@*/

// Auxiliary definitions for the project & split operation

/*@

fixpoint bool cat_getchar_allowed(catstate s, getchar_action a) {
    switch (s) {
        case catstate(eof, read, written): return
            switch (a) {
                case getchar_action: return !eof;
                case getchar_return_action(result): return true;
            };
    }
}

fixpoint catstate cat_getchar_next(catstate s, getchar_action a) {
    switch (s) {
        case catstate(eof, read, written): return
            switch (a) {
                case getchar_action: return s;
                case getchar_return_action(result): return 0 <= result ? catstate(eof, cons((char)result, read), written) : catstate(true, read, written);
            };
    }
}

fixpoint bool cat_putchar_allowed(catstate s, putchar_action a) {
    switch (s) {
        case catstate(eof, read, written): return
            switch (a) {
                case putchar_action(c): return is_suffix_of(cons(c, written), read);
                case putchar_return_action: return true;
            };
    }
}

fixpoint catstate cat_putchar_next(catstate s, putchar_action a) {
    switch (s) {
        case catstate(eof, read, written): return
            switch (a) {
                case putchar_action(c): return catstate(eof, read, cons(c, written));
                case putchar_return_action: return s;
            };
    }
}

fixpoint bool cat_sim(catstate s0, pair<catstate, catstate> s) {
    switch (s0) {
        case catstate(eof0, read0, written0): return
            switch (s) {
                case pair(sg, sp): return
                    switch (sg) {
                        case catstate(eofg, readg, writteng): return
                            switch (sp) {
                                case catstate(eofp, readp, writtenp): return
                                    eof0 == eofg && read0 == readg && written0 == writtenp && is_suffix_of(readp, read0);
                            };
                    };
            };
    }
}

lemma void cat_is_sim(catstate s1, pair<catstate, catstate> s2, sum<getchar_action, putchar_action> a)
    requires
        cat_sim(s1, s2) == true &*&
        lift_sum(getchar_action_is_out, putchar_action_is_out, a) ?
            lift_allowed(cat_getchar_allowed, cat_putchar_allowed, s2, a) == true
        :
            cat_allowed(s1, a) == true;
    ensures
        cat_allowed(s1, a) == true &*&
        lift_allowed(cat_getchar_allowed, cat_putchar_allowed, s2, a) == true &*&
        cat_sim(cat_next(s1, a), lift_next(cat_getchar_next, cat_putchar_next, s2, a)) == true;
{
    switch (s1) {
        case catstate(eof, read, written):
            switch (s2) {
                case pair(sg, sp):
                    switch (sg) {
                        case catstate(eofg, readg, writteng):
                            switch (sp) {
                                case catstate(eofp, readp, writtenp):
                                    switch (a) {
                                        case left(ag):
                                            switch (ag) {
                                                case getchar_action:
                                                    return;
                                                case getchar_return_action(result):
                                                    return;
                                            }
                                        case right(ap):
                                            switch (ap) {
                                                case putchar_action(c):
                                                    is_suffix_of_trans(cons(c, writtenp), readp, read);
                                                    return;
                                                case putchar_return_action:
                                                    return;
                                            }
                                    }
                            }
                    }
            }
    }
}

@*/

void cat()
    /*@
    requires
        world<sum<getchar_action, putchar_action>, catstate>(
            ?id, (lift_sum)(getchar_action_is_out, putchar_action_is_out), catstate(false, nil, nil), cat_allowed, cat_next);
    @*/
    /*@
    ensures
        world<sum<getchar_action, putchar_action>, catstate>(
            id, (lift_sum)(getchar_action_is_out, putchar_action_is_out), ?s, cat_allowed, cat_next) &*&
        switch (s) { case catstate(eof, read, written): return eof == true &*& written == read; };
    @*/
{
    for (;;)
        /*@
        invariant
            world<sum<getchar_action, putchar_action>, catstate>(
                id, (lift_sum)(getchar_action_is_out, putchar_action_is_out), ?s, cat_allowed, cat_next) &*&
            switch (s) { case catstate(eof, read, written): return !eof &*& written == read; };
        @*/
    {
        //@ produce_lemma_function_pointer_chunk(cat_is_sim) : is_sim<sum<getchar_action, putchar_action>, catstate, pair<catstate, catstate> >((lift_sum)(getchar_action_is_out, putchar_action_is_out), cat_allowed, cat_next, (lift_allowed)(cat_getchar_allowed, cat_putchar_allowed), (lift_next)(cat_getchar_next, cat_putchar_next), cat_sim)(s1, s2, a) { call(); };
        //@ switch (s) { case catstate(eof, read, written): is_suffix_of_refl(read); }
        //@ project_world((lift_allowed)(cat_getchar_allowed, cat_putchar_allowed), (lift_next)(cat_getchar_next, cat_putchar_next), cat_sim, cat_is_sim, pair(s, s));
        //@ leak is_is_sim(_, _, _, _, _, _, _);
        //@ split_world(getchar_action_is_out, s, cat_getchar_allowed, cat_getchar_next, putchar_action_is_out, s, cat_putchar_allowed, cat_putchar_next);
        int c = getchar();
        //@ unsplit_world();
        //@ unproject_world();
        
        if (c < 0) return;
        
        //@ produce_lemma_function_pointer_chunk(cat_is_sim) : is_sim<sum<getchar_action, putchar_action>, catstate, pair<catstate, catstate> >((lift_sum)(getchar_action_is_out, putchar_action_is_out), cat_allowed, cat_next, (lift_allowed)(cat_getchar_allowed, cat_putchar_allowed), (lift_next)(cat_getchar_next, cat_putchar_next), cat_sim)(s1, s2, a) { call(); };
        //@ assert world<sum<getchar_action, putchar_action>, catstate>(_, _, ?s1, _, _);
        //@ switch (s1) { case catstate(eof, read, written): is_suffix_of_refl(read); }
        //@ project_world((lift_allowed)(cat_getchar_allowed, cat_putchar_allowed), (lift_next)(cat_getchar_next, cat_putchar_next), cat_sim, cat_is_sim, pair(s1, s1));
        //@ leak is_is_sim(_, _, _, _, _, _, _);
        //@ split_world(getchar_action_is_out, s1, cat_getchar_allowed, cat_getchar_next, putchar_action_is_out, s1, cat_putchar_allowed, cat_putchar_next);
        putchar((char)c);
        //@ unsplit_world();
        //@ unproject_world();
    }
}
