//@ #include <strong_ghost_lists.gh>
//@ #include "ghost_lists.gh"

/*@

predicate ghost_list_member_handle<t>(int id, t x) = strong_ghost_list_member_handle(id, x);
predicate ghost_list_member_handles<t>(int id, list<t> xs) =
    switch (xs) {
    case nil: return true;
    case cons(x0, xs0): return [_]ghost_list_member_handle(id, x0) &*& ghost_list_member_handles(id, xs0);
    };
predicate ghost_list<t>(int id, list<t> xs) =
    strong_ghost_list<t>(id, xs) &*& ghost_list_member_handles(id, xs);

lemma int create_ghost_list<t>()
    requires true;
    ensures ghost_list<t>(result, nil);
{
    int id = create_strong_ghost_list<t>();
    close ghost_list_member_handles<t>(id, nil);
    close ghost_list<t>(id, nil);
    return id;
}

lemma void ghost_list_add<t>(int id, t x)
    requires ghost_list<t>(id, ?xs);
    ensures ghost_list(id, cons(x, xs)) &*& [_]ghost_list_member_handle(id, x);
{
    open ghost_list<t>(id, xs);
    strong_ghost_list_insert(id, nil, xs, x);
    close ghost_list_member_handle(id, x);
    leak ghost_list_member_handle(id, x);
    close ghost_list_member_handles(id, cons(x, xs));
    close ghost_list<t>(id, cons(x, xs));
}

lemma void ghost_list_member_handle_lemma<t>(int id)
    requires [?f1]ghost_list<t>(id, ?xs) &*& [?f2]ghost_list_member_handle<t>(id, ?x);
    ensures [f1]ghost_list(id, xs) &*& [f2]ghost_list_member_handle(id, x) &*& mem(x, xs) == true;
{
    open ghost_list(id, xs);
    open ghost_list_member_handle(id, x);
    strong_ghost_list_member_handle_lemma();
    close [f2]ghost_list_member_handle(id, x);
    close [f1]ghost_list(id, xs);
}

lemma void ghost_list_member_handles_extract<t>(t x)
    requires [?f]ghost_list_member_handles<t>(?id, ?xs) &*& mem(x, xs) == true;
    ensures [f]ghost_list_member_handles<t>(id, xs) &*& [_]ghost_list_member_handle(id, x);
{
    open [f]ghost_list_member_handles(id, xs);
    switch (xs) {
    case nil:
    case cons(x0, xs0):
        if (x0 == x) {
        } else {
            ghost_list_member_handles_extract(x);
        }
    }
    close [f]ghost_list_member_handles(id, xs);
}

lemma void ghost_list_create_member_handle<t>(int id, t x)
    requires [?f1]ghost_list(id, ?xs) &*& mem(x, xs) == true;
    ensures [f1]ghost_list(id, xs) &*& [_]ghost_list_member_handle(id, x);
{
    open [f1]ghost_list(id, xs);
    ghost_list_member_handles_extract(x);
    close [f1]ghost_list(id, xs);
}

predicate ghost_assoc_list(int id, list<pair<void *, void *> > xs) = ghost_list(id, map(fst, xs));
predicate ghost_assoc_list_member_handle(int id, void **pp) = ghost_list_member_handle<void *>(id, pp);

lemma int create_ghost_assoc_list()
    requires true;
    ensures ghost_assoc_list(result, nil);
{
    int id = create_ghost_list<void *>();
    close ghost_assoc_list(id, nil);
    return id;
}

lemma void ghost_assoc_list_add(int id, void *x, void *y)
    requires ghost_assoc_list(id, ?xys);
    ensures ghost_assoc_list(id, cons(pair(x, y), xys));
{
    open ghost_assoc_list(id, xys);
    ghost_list_add(id, x);
    close ghost_assoc_list(id, cons(pair(x, y), xys));
}

lemma void map_fst_update_assoc<a, b>(list<pair<a, b> > xys, a x, b y)
    requires true;
    ensures map(fst, update_assoc(xys, x, y)) == map(fst, xys);
{
    switch (xys) {
    case nil:
    case cons(xy0, xys0):
        assert xy0 == pair(?x0, ?y0);
        if (x0 == x) {
        } else {
            map_fst_update_assoc(xys0, x, y);
        }
    }
}

lemma void ghost_assoc_list_update(int id, void **x, void *y)
    requires ghost_assoc_list(id, ?xys) &*& mem_assoc(x, xys) == true;
    ensures ghost_assoc_list(id, update_assoc(xys, x, y));
{
    open ghost_assoc_list(id, xys);
    map_fst_update_assoc(xys, x, y);
    close ghost_assoc_list(id, update_assoc(xys, x, y));
}

lemma void ghost_assoc_list_create_member_handle(int id, void **x)
    requires [?f1]ghost_assoc_list(id, ?xys) &*& mem_assoc(x, xys) == true;
    ensures [f1]ghost_assoc_list(id, xys) &*& [_]ghost_assoc_list_member_handle(id, x);
{
    open [f1]ghost_assoc_list(id, xys);
    ghost_list_create_member_handle(id, x);
    close [f1]ghost_assoc_list(id, xys);
    assert [?f]ghost_list_member_handle(id, x);
    close [f]ghost_assoc_list_member_handle(id, x);
}

lemma void ghost_assoc_list_member_handle_lemma(int id, void **x)
    requires [?f1]ghost_assoc_list(id, ?xys) &*& [?f2]ghost_assoc_list_member_handle(id, x);
    ensures [f1]ghost_assoc_list(id, xys) &*& [f2]ghost_assoc_list_member_handle(id, x) &*& mem_assoc(x, xys) == true;
{
    open [f1]ghost_assoc_list(id, xys);
    open [f2]ghost_assoc_list_member_handle(id, x);
    ghost_list_member_handle_lemma(id);
    close [f1]ghost_assoc_list(id, xys);
    close [f2]ghost_assoc_list_member_handle(id, x);
}

@*/