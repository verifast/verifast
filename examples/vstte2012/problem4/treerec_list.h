#ifndef TREEREC_LIST_H
#define TREEREC_LIST_H

struct list;

//@ predicate list(struct list *l; list<int> values);

struct list *create_list();
    //@ requires true;
    //@ ensures list(result, nil);

void list_push(struct list *list, int value);
    //@ requires list(list, ?values);
    //@ ensures list(list, cons(value, values));

bool list_is_empty(struct list *list);
    //@ requires list(list, ?values);
    //@ ensures list(list, values) &*& switch (values) { case nil: return result == true; case cons(h, t): return result == false; };

int list_head(struct list *list);
    //@ requires list(list, ?values) &*& values != nil;
    //@ ensures list(list, values) &*& result == head(values);

int list_pop(struct list *list);
    //@ requires list(list, ?values) &*& values != nil;
    //@ ensures list(list, tail(values)) &*& result == head(values);

void list_dispose(struct list *list);
    //@ requires list(list, ?values);
    //@ ensures true;

#endif