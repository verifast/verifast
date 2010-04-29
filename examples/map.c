#include "stdlib.h"
#include "assert.h"

struct node {
    struct node *next;
    int value;
};

/*@

predicate list(struct node *l, list<int> xs) =
    l == 0 ? xs == nil : l->value |-> ?value &*& l->next |-> ?next &*& malloc_block_node(l) &*& list(next, ?tail) &*& xs == cons(value, tail);

@*/

struct node *list_cons(int value, struct node *next)
    //@ requires list(next, ?tail);
    //@ ensures list(result, cons(value, tail));
{
    struct node *result = (struct node *)malloc(sizeof(struct node)); // Include the cast to make it a valid C++ program
    if (result == 0) { abort(); }
    result->value = value;
    result->next = next;
    //@ close list(result, cons(value, tail));
    return result;
}

bool equals(struct node *n1, struct node *n2)
    //@ requires list(n1, ?xs1) &*& list(n2, ?xs2);
    //@ ensures list(n1, xs1) &*& list(n2, xs2) &*& result ? xs1 == xs2 : xs1 != xs2;
{
    //@ open list(n1, xs1);
    //@ open list(n2, xs2);
    bool result = false;
    if (n1 == 0)
        result = n2 == 0;
    else if (n2 == 0)
        result = false;
    else if (n1->value != n2->value)
        result = false;
    else {
        bool tmp = equals(n1->next, n2->next);
        result = tmp;
    }
    //@ close list(n1, xs1);
    //@ close list(n2, xs2);
    return result;
}

void dispose(struct node *l)
    //@ requires list(l, _);
    //@ ensures true;
{
    //@ open list(l, _);
    if (l != 0) {
        struct node *next = l->next;
        free(l);
        dispose(next);
    }
}

/*@

predicate_family mapfunc(void *mapfunc)(void *data, list<int> in, list<int> out, any info);

@*/

typedef int mapfunc(void *data, int x);
    //@ requires mapfunc(this)(data, ?in, ?out, ?info) &*& in != nil &*& x == head(in);
    //@ ensures mapfunc(this)(data, tail(in), append(out, cons(result, nil)), info);

struct node *fmap(struct node *list, mapfunc *f, void *data)
    //@ requires list(list, ?xs) &*& is_mapfunc(f) == true &*& mapfunc(f)(data, xs, ?out, ?info);
    //@ ensures list(list, xs) &*& list(result, ?ys) &*& mapfunc(f)(data, nil, append(out, ys), info);
{
    //@ open list(list, xs);
    if (list == 0) {
        //@ close list(list, xs);
        //@ close list(0, nil);
        //@ append_nil(out);
        return 0;
    } else {
        int fvalue = f(data, list->value);
        struct node *fnext = fmap(list->next, f, data);
        //@ assert list(fnext, ?ftail);
        //@ close list(list, xs);
        struct node *result = list_cons(fvalue, fnext);
        //@ append_assoc(out, cons(fvalue, nil), ftail);
        return result;
    }
}

/*@

fixpoint int plusOne(unit u, int x) {
    switch (u) {
        case unit: return x + 1;
    }
}

predicate_family_instance mapfunc(plusOneFunc)(void *data, list<int> in, list<int> out, list<int> info) =
    map((plusOne)(unit), info) == append(out, map((plusOne)(unit), in));

@*/

int plusOneFunc(void *data, int x) //@ : mapfunc
    //@ requires mapfunc(plusOneFunc)(data, ?in, ?out, ?info) &*& in != nil &*& x == head(in);
    //@ ensures mapfunc(plusOneFunc)(data, tail(in), append(out, cons(result, nil)), info);
{
    if (x == 2147483647) abort();
    //@ open mapfunc(plusOneFunc)(data, in, out, ?info_);
    //@ append_assoc(out, cons(x + 1, nil), map((plusOne)(unit), tail(in)));
    //@ switch (in) { case nil: case cons(h, t): }
    //@ close mapfunc(plusOneFunc)(data, tail(in), append(out, cons(x + 1, nil)), info_);
    return x + 1;
}

int main() //@ : main
    //@ requires true;
    //@ ensures true;
{
    struct node *l = 0;
    //@ close list(0, nil);
    l = list_cons(3, l);
    l = list_cons(2, l);
    l = list_cons(1, l);
    //@ close mapfunc(plusOneFunc)(0, cons(1, cons(2, cons(3, nil))), nil, cons(1, cons(2, cons(3, nil))));
    struct node *l2 = fmap(l, plusOneFunc, 0);
    //@ open mapfunc(plusOneFunc)(0, nil, ?ys, _);
    struct node *l3 = 0;
    //@ close list(0, nil);
    l3 = list_cons(4, l3);
    l3 = list_cons(3, l3);
    l3 = list_cons(2, l3);
    bool tmp = equals(l2, l3);
    //@ append_nil(ys);
    assert(tmp);
    dispose(l);
    dispose(l2);
    dispose(l3);
    return 0;
}
