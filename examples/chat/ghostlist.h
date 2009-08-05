#ifndef GHOST_LISTS_H
#define GHOST_LISTS_H

#include "lists.h"

/*@

predicate ghost_list<t>(int id, list<t> xs);
predicate ghost_list_member_handle<t>(int id, t d);

lemma int create_ghost_list<t>();
    requires true;
    ensures ghost_list<t>(result, nil);

lemma void ghost_list_add<t>(int id, t d);
    requires ghost_list<t>(id, ?ds);
    ensures ghost_list<t>(id, cons(d, ds)) &*& ghost_list_member_handle<t>(id, d);
    
lemma void ghost_list_remove<t>(int id, t d);
    requires ghost_list<t>(id, ?ds) &*& ghost_list_member_handle<t>(id, d);
    ensures ghost_list<t>(id, remove(d, ds));

lemma void ghost_list_member_handle_lemma<t>();
    requires [?f1]ghost_list<t>(?id, ?ds) &*& [?f2]ghost_list_member_handle<t>(id, ?d);
    ensures [f1]ghost_list<t>(id, ds) &*& [f2]ghost_list_member_handle<t>(id, d) &*& mem(d, ds) == true;
@*/

#endif