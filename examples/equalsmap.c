#include "stdlib.h"

struct node {
    struct node *next;
    void *key;
    void *value;
};

/*@

predicate map(struct node *n; list<pair<void *, void *> > entries) =
    n == 0 ?
        entries == nil
    :
        n->next |-> ?next &*& n->key |-> ?key &*& n->value |-> ?value &*& malloc_block_node(n) &*&
        map(next, ?entriesTail) &*& entries == cons(pair(key, value), entriesTail);

@*/

struct node *map_nil()
    //@ requires true;
    //@ ensures map(result, nil);
{
    return 0;
}

struct node *map_cons(void *key, void *value, struct node *tail)
    //@ requires map(tail, ?tailEntries);
    //@ ensures map(result, cons(pair(key, value), tailEntries));
{
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) abort();
    n->key = key;
    n->value = value;
    n->next = tail;
    return n;
}

void map_dispose(struct node *map)
    //@ requires map(map, _);
    //@ ensures true;
{
    //@ open map(map, _);
    if (map != 0) {
        map_dispose(map->next);
        free(map);
    }
}

typedef bool equalsFuncType/*@ (list<void *> keys, void *key00, list<void *> eqKeys, predicate() p) @*/(void *key, void *key0);
    //@ requires p() &*& mem(key, keys) == true &*& key0 == key00;
    //@ ensures p() &*& result == contains(eqKeys, key);

/*@

fixpoint bool eq<t>(unit u, t x, t y) {
    switch (u) {
        case unit: return x == y;
    }
}

fixpoint bool contains<t>(list<t> xs, t x) {
    switch (xs) {
        case nil: return false;
        case cons(x0, xs0): return x0 == x || contains(xs0, x);
    }
}

fixpoint bool is_suffix_of<t>(list<t> xs, list<t> ys) {
    switch (ys) {
        case nil: return xs == ys;
        case cons(y, ys0): return xs == ys || is_suffix_of(xs, ys0);
    }
}

lemma void is_suffix_of_mem<t>(list<t> xs, list<t> ys, t y)
    requires is_suffix_of(xs, ys) == true &*& mem(y, xs) == true;
    ensures mem(y, ys) == true;
{
    switch (ys) {
        case nil:
        case cons(y0, ys0):
            if (xs == ys) {
            } else {
                if (y0 == y) {
                } else {
                    is_suffix_of_mem(xs, ys0, y);
                }
            }
    }
}

lemma void is_suffix_of_trans<t>(list<t> xs, list<t> ys, list<t> zs)
    requires is_suffix_of(xs, ys) == true &*& is_suffix_of(ys, zs) == true;
    ensures is_suffix_of(xs, zs) == true;
{
    switch (zs) {
        case nil:
        case cons(z, zs0):
            if (zs == ys) {
            } else {
                is_suffix_of_trans(xs, ys, zs0);
            }
    }
}

lemma_auto void is_suffix_of_refl<t>(list<t> xs)
    requires true;
    ensures is_suffix_of(xs, xs) == true;
{
    switch (xs) {
        case nil:
        case cons(x, xs0):
    }
}

@*/

bool map_contains_key(struct node *map, void *key, equalsFuncType *equalsFunc)
    //@ requires [_]is_equalsFuncType(equalsFunc, ?keys, key, ?eqKeys, ?p) &*& p() &*& map(map, ?entries) &*& is_suffix_of(map((fst), entries), keys) == true;
    //@ ensures p() &*& map(map, entries) &*& result == exists(map((fst), entries), (contains)(eqKeys));
{
    //@ open map(map, _);
    if (map == 0)
        return false;
    else {
        //@ is_suffix_of_mem(map((fst), entries), keys, map->key);
        bool eq = equalsFunc(map->key, key);
        if (eq)
            return true;
        else {
            //@ assert is_suffix_of(map((fst), tail(entries)), map((fst), entries)) == true;
            //@ is_suffix_of_trans(map((fst), tail(entries)), map((fst), entries), keys);
            return map_contains_key(map->next, key, equalsFunc);
        }
    }
}

struct foo {
    int value;
};

/*@

predicate foo(pair<struct foo *, int> fv;) =
    switch (fv) {
        case pair(f, v): return f->value |-> v;
    };

predicate_ctor foos_ctor(list<pair<struct foo *, int> > fvs, struct foo *f, int value)() =
    foreach(fvs, foo) &*& f->value |-> value;

fixpoint b assoc<a, b>(list<pair<a, b> > xys, a x) {
    switch (xys) {
        case nil: return default_value;
        case cons(xy, xys0): return fst(xy) == x ? snd(xy) : assoc(xys0, x);
    }
}

@*/

bool foo_equals(struct foo *f1, struct foo *f2)
    //@ requires foreach(?fvs, foo) &*& f2->value |-> ?value &*& mem(pair(f1, assoc(fvs, f1)), fvs) == true;
    //@ ensures foreach(fvs, foo) &*& f2->value |-> value &*& result == (assoc(fvs, f1) == value);
{
    //@ foreach_remove(pair(f1, assoc(fvs, f1)), fvs);
    //@ open foo(pair(f1, assoc(fvs, f1)));
    return f1->value == f2->value;
    //@ close foo(pair(f1, assoc(fvs, f1)));
    //@ foreach_unremove(pair(f1, assoc(fvs, f1)), fvs);
}

struct foo *create_foo(int value)
    //@ requires true;
    //@ ensures result->value |-> value &*& malloc_block_foo(result);
{
    struct foo *foo = malloc(sizeof(struct foo));
    if (foo == 0) abort();
    foo->value = value;
    return foo;
}

int main()
    //@ requires true;
    //@ ensures true;
{
    struct foo *foo1 = create_foo(100);
    struct foo *foo2 = create_foo(200);
    struct foo *foo3 = create_foo(300);
    struct node *map = map_nil();
    map = map_cons(foo3, 0, map);
    map = map_cons(foo2, 0, map);
    map = map_cons(foo1, 0, map);
    struct foo *fooX = create_foo(200);
    struct foo *fooY = create_foo(400);
    //@ list<pair<struct foo *, int> > fvs = cons(pair(foo1, 100), cons(pair(foo2, 200), cons(pair(foo3, 300), nil)));
    /*@
    produce_function_pointer_chunk
        equalsFuncType(foo_equals)(cons(foo1, cons(foo2, cons(foo3, nil))), fooX, cons(foo2, nil), foos_ctor(fvs, fooX, 200))
            (f1, f2) {
        open foos_ctor(fvs, fooX, 200)();
        bool result = call();
        close foos_ctor(fvs, fooX, 200)();
        if (result) {} else {}
    }
    @*/
    //@ close foreach(nil, foo);
    //@ close foo(pair(foo3, 300));
    //@ close foreach(cons(pair(foo3, 300), nil), foo);
    //@ close foo(pair(foo2, 200));
    //@ close foreach(cons(pair(foo2, 200), cons(pair(foo3, 300), nil)), foo);
    //@ close foo(pair(foo1, 100));
    //@ close foreach(cons(pair(foo1, 100), cons(pair(foo2, 200), cons(pair(foo3, 300), nil))), foo);
    //@ close foos_ctor(fvs, fooX, 200)();
    bool c = map_contains_key(map, fooX, foo_equals);
    assert(c);
    /*@
    produce_function_pointer_chunk
        equalsFuncType(foo_equals)(cons(foo1, cons(foo2, cons(foo3, nil))), fooY, nil, foos_ctor(fvs, fooY, 400))
            (f1, f2) {
        open foos_ctor(fvs, fooY, 400)();
        call();
        close foos_ctor(fvs, fooY, 400)();
    }
    @*/
    //@ open foos_ctor(fvs, fooX, 200)();
    //@ close foos_ctor(fvs, fooY, 400)();
    c = map_contains_key(map, fooY, foo_equals);
    assert(!c);
    //@ open foos_ctor(fvs, fooY, 400)();
    //@ open foreach(_, foo);
    //@ open foo(_);
    //@ open foreach(_, foo);
    //@ open foo(_);
    //@ open foreach(_, foo);
    //@ open foo(_);
    //@ open foreach(_, foo);
    free(foo1);
    free(foo2);
    free(foo3);
    free(fooX);
    free(fooY);
    map_dispose(map);
    return 0;
}
