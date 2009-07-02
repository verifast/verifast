#ifndef GHOST_LISTS_H
#define GHOST_LISTS_H

#include "lists.h"

/*@

predicate ghost_list(int id, listval xs);
predicate ghost_list_member_handle(int id, void *d);

lemma int create_ghost_list();
    requires true;
    ensures ghost_list(result, nil);

lemma void ghost_list_add(int id, void *d);
    requires ghost_list(id, ?ds);
    ensures ghost_list(id, cons(d, ds)) &*& ghost_list_member_handle(id, d);
    
lemma void ghost_list_remove(int id, void *d);
    requires ghost_list(id, ?ds) &*& ghost_list_member_handle(id, d);
    ensures ghost_list(id, remove(ds, d));

lemma void ghost_list_member_handle_lemma();
    requires [?f1]ghost_list(?id, ?ds) &*& [?f2]ghost_list_member_handle(id, ?d);
    ensures [f1]ghost_list(id, ds) &*& [f2]ghost_list_member_handle(id, d) &*& contains(ds, d) == true;
@*/

#endif