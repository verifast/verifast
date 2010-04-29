/*@

inductive io_action =
  getchar_action
| getchar_return_action(int)
| putchar_action(char)
| putchar_return_action;

predicate world<s>(s state, fixpoint(s, io_action, bool) allowed, fixpoint(s, io_action, s) next);

@*/

int getchar/*@ <s> @*/();
    //@ requires world<s>(?s, ?allowed, ?next) &*& allowed(s, getchar_action) == true;
    /*@
    ensures
        allowed(next(s, getchar_action), getchar_return_action(result)) == true &*&
        world<s>(next(next(s, getchar_action), getchar_return_action(result)), allowed, next);
    @*/

void putchar/*@ <s> @*/(char c);
    //@ requires world<s>(?s, ?allowed, ?next) &*& allowed(s, putchar_action(c)) == true;
    /*@
    ensures
        allowed(next(s, putchar_action(c)), putchar_return_action) == true &*&
        world<s>(next(next(s, putchar_action(c)), putchar_return_action), allowed, next);
    @*/

// helloworld

// The LTS state is the list of characters that have yet to be written.

/*@

fixpoint bool helloworld_allowed(list<char> s, io_action a) {
    switch (a) {
        case getchar_action: return false;
        case getchar_return_action(result): return true;
        case putchar_action(c): return s != nil && head(s) == c;
        case putchar_return_action: return true;
    }
}

fixpoint list<char> helloworld_next(list<char> s, io_action a) {
    switch (a) {
        case getchar_action: return s;
        case getchar_return_action(result): return s;
        case putchar_action(c): return tail(s);
        case putchar_return_action: return s;
    }
}

@*/

void helloworld()
    //@ requires world<list<char> >(cons('H', cons('e', /*...*/ cons('\n', nil))), helloworld_allowed, helloworld_next);
    //@ ensures world(nil, helloworld_allowed, helloworld_next);
{
    putchar('H');
    putchar('e');
    // ...
    putchar('\n');
}

// cat

/*@

fixpoint bool is_suffix_of<t>(list<t> xs, list<t> ys) {
    switch (ys) {
        case nil: return xs == ys;
        case cons(y, ys0): return xs == ys || is_suffix_of(xs, ys0);
    }
}

inductive cat_state = cat_state(bool eof, list<char> read, list<char> written);

fixpoint bool cat_allowed(cat_state s, io_action a) {
    switch (s) {
        case cat_state(eof, read, written): return
            switch (a) {
                case getchar_action: return !eof;
                case getchar_return_action(result): return true;
                case putchar_action(c): return is_suffix_of(cons(c, written), read);
                case putchar_return_action: return true;
            };
    }
}

fixpoint cat_state cat_next(cat_state s, io_action a) {
    switch (s) {
        case cat_state(eof, read, written): return
            switch (a) {
                case getchar_action: return s;
                case getchar_return_action(result): return 0 <= result ? cat_state(eof, cons((char)result, read), written) : cat_state(true, read, written);
                case putchar_action(c): return cat_state(eof, read, cons(c, written));
                case putchar_return_action: return s;
            };
    }
}

@*/

void cat()
    //@ requires world(cat_state(false, nil, nil), cat_allowed, cat_next);
    //@ ensures world<cat_state>(?s, cat_allowed, cat_next) &*& switch (s) { case cat_state(eof, read, written): return eof == true &*& written == read; };
{
    for (;;)
        //@ invariant world<cat_state>(?s, cat_allowed, cat_next) &*& switch (s) { case cat_state(eof, read, written): return !eof &*& written == read; };
    {
        int c = getchar();
        if (c < 0) return;
        putchar((char)c);
    }
}
