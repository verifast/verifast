/*@

inductive io_action = putchar_action(char) | putchar_return_action;

// This state machine might be a projection of another state machine; the id identifies the projection.

predicate world<s>(int id, s state, fixpoint(s, io_action, bool) allowed, fixpoint(s, io_action, s) next);

typedef lemma void is_sim<s1, s2>(
        fixpoint(s1, io_action, bool) allowed1, fixpoint(s1, io_action, s1) next1,
        fixpoint(s2, io_action, bool) allowed2, fixpoint(s2, io_action, s2) next2,
        fixpoint(s1, s2, bool) sim
    )(s1 s1, s2 s2, io_action a);
    requires sim(s1, s2) == true &*& switch (a) { case putchar_action(c): return allowed2(s2, a) == true; case putchar_return_action: return allowed1(s1, a) == true; };
    ensures allowed1(s1, a) == true &*& allowed2(s2, a) == true &*& sim(next1(s1, a), next2(s2, a)) == true;

predicate unproject_token<s1, s2>(int id_new, int id_old, fixpoint(s1, io_action, bool) allowed, fixpoint(s1, io_action, s1) next, fixpoint(s1, s2, bool) sim);

lemma int project_world<s1, s2>(fixpoint(s2, io_action, bool) allowed2, fixpoint(s2, io_action, s2) next2, fixpoint(s1, s2, bool) sim, is_sim *is_sim, s2 s_new);
    requires
        world<s1>(?id_old, ?s_old, ?allowed1, ?next1) &*&
        is_is_sim<s1, s2>(is_sim, allowed1, next1, allowed2, next2, sim) &*&
        sim(s_old, s_new) == true;
    ensures
        world<s2>(result, s_new, allowed2, next2) &*&
        is_is_sim<s1, s2>(is_sim, allowed1, next1, allowed2, next2, sim) &*&
        unproject_token<s1, s2>(result, id_old, allowed1, next1, sim);

lemma void unproject_world<s1, s2>();
    requires world<s2>(?id_new, ?s_new, ?allowed2, ?next2) &*& unproject_token<s1, s2>(id_new, ?id_old, ?allowed1, ?next1, ?sim);
    ensures world<s1>(id_old, ?s_old, allowed1, next1) &*& sim(s_old, s_new) == true;

@*/

/*@

inductive putchar_state = putchar_before(char) | putchar_after;

fixpoint bool putchar_allowed(putchar_state s, io_action a) {
    switch (a) {
        case putchar_action(c): return s == putchar_before(c);
        case putchar_return_action: return true;
    }
}

fixpoint putchar_state putchar_next(putchar_state s, io_action a) {
    switch (s) {
        case putchar_before(c): return switch (a) { case putchar_action(c0): return putchar_after; case putchar_return_action: return putchar_before(c); };
        case putchar_after: return putchar_after;
    }
}

@*/

void putchar(char c);
    //@ requires world(?id, putchar_before(c), putchar_allowed, putchar_next);
    //@ ensures world(id, putchar_after, putchar_allowed, putchar_next);

/*@

fixpoint bool myputn_allowed(int s, io_action a) {
    switch (a) {
        case putchar_action(c): return 0 < s;
        case putchar_return_action: return true;
    }
}

fixpoint int myputn_next(int s, io_action a) {
    switch (a) {
        case putchar_action(c): return s - 1;
        case putchar_return_action: return s;
    }
}

@*/

/*@

fixpoint bool myput2_sim(int offset, int s1, putchar_state s2) {
    switch (s2) {
        case putchar_before(c): return s1 == offset + 1;
        case putchar_after: return s1 == offset;
    }
}

predicate myput2_offset(int offset) = true;

lemma void myput2_is_sim(int s1, putchar_state s2, io_action a)
    requires myput2_offset(?offset) &*& 0 <= offset &*& true == (myput2_sim)(offset, s1, s2) &*& switch (a) { case putchar_action(c): return putchar_allowed(s2, a) == true; case putchar_return_action: return myputn_allowed(s1, a) == true; };
    ensures myputn_allowed(s1, a) == true &*& putchar_allowed(s2, a) == true &*& myput2_sim(offset, myputn_next(s1, a), putchar_next(s2, a)) == true;
{
    open myput2_offset(_);
    switch (s2) {
        case putchar_before(c):
        case putchar_after:
    }
}

@*/

void myput2(char c)
    //@ requires world(?id, 2, myputn_allowed, myputn_next);
    //@ ensures world(id, 0, myputn_allowed, myputn_next);
{
    //@ produce_lemma_function_pointer_chunk(myput2_is_sim) : is_sim<int, putchar_state>(myputn_allowed, myputn_next, putchar_allowed, putchar_next, (myput2_sim)(1))(s1, s2, a) { close myput2_offset(1); call(); };
    //@ project_world(putchar_allowed, putchar_next, (myput2_sim)(1), myput2_is_sim, putchar_before(c));
    //@ leak is_is_sim(_, _, _, _, _, _);
    putchar(c);
    //@ unproject_world();
    //@ produce_lemma_function_pointer_chunk(myput2_is_sim) : is_sim<int, putchar_state>(myputn_allowed, myputn_next, putchar_allowed, putchar_next, (myput2_sim)(0))(s1, s2, a) { close myput2_offset(0); call(); };
    //@ project_world(putchar_allowed, putchar_next, (myput2_sim)(0), myput2_is_sim, putchar_before(c));
    //@ leak is_is_sim(_, _, _, _, _, _);
    putchar(c);
    //@ unproject_world();
}
