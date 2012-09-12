/*
    A sequential implementation of linkedlists 
*/
#ifndef LINKEDLIST_H
#define LINKEDLIST_H

//@ #include "listex2.gh"


struct linkedlist;

/*@
predicate linkedlist(struct linkedlist* list; list<void*> elems);
@*/

struct linkedlist* linkedlist_create();
    //@requires true;
    //@ensures linkedlist(result, nil);

void linkedlist_dispose(struct linkedlist* list);
    //@requires linkedlist(list, ?elems);
    //@ensures true;

void linkedlist_add(struct linkedlist* list, void* elem);
    //@requires linkedlist(list, ?elems);
    //@ensures linkedlist(list, cons(elem, elems));

void linkedlist_add_end(struct linkedlist* list, void* elem);
    //@requires linkedlist(list, ?elems);
    //@ensures linkedlist(list, snoc(elems, elem));

void linkedlist_remove(struct linkedlist* list, void* elem);
    //@requires linkedlist(list, ?elems);
    //@ensures linkedlist(list, remove(elem, elems));

bool linkedlist_contains(struct linkedlist* list, void* elem);
    //@requires linkedlist(list, ?elems);
    //@ensures linkedlist(list, elems) &*& result == mem(elem, elems);

bool linkedlist_is_empty(struct linkedlist* list);
    //@requires linkedlist(list, ?elems);
    //@ensures linkedlist(list, elems) &*& result == (elems == nil);

int linkedlist_count(struct linkedlist* list);
    //@requires linkedlist(list, ?elems);
    //@ensures linkedlist(list, elems) &*& result == length(elems);
    
void* linkedlist_pop(struct linkedlist* list);
    //@requires linkedlist(list, ?elems) &*& elems != nil;
    //@ensures linkedlist(list, tail(elems)) &*& result == head(elems);

#endif