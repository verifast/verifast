#include "atomics.h"
//@ #include "space_user.gh"
//@ #include "ghost_cells.gh"
//@ #include "fraction_store.gh"
//@ #include "ghost_params.gh"
//@ #include "listex2.gh"

/*

This example shows how you can make sure that an atomic space can not be disposed before 
it has no more users left.

*/

/*@

predicate dispose_perm(int id;) = 
    [_]ghost_cell<pair<int, int> >(id, ?info) &*&
    ghost_cell<unit>(fst(info), unit);

lemma void dispose_perm_unique(int id)
    requires [?f]dispose_perm(id);
    ensures [f]dispose_perm(id) &*& f <= 1;
{
    open [f]dispose_perm(id);
    assert [_]ghost_cell<pair<int, int> >(id, ?info);
    ghost_cell_fraction_info<unit>(fst(info));
    close [f]dispose_perm(id);
}

predicate dispose_perm_helper(int id; unit u) = 
    dispose_perm(id) &*& u == unit;

lemma void dispose_perm_helper_unique(int id) //: predicate_unique<int, unit>(dispose_perm_helper)
    requires [?f]dispose_perm_helper(id, ?b);
    ensures [f]dispose_perm_helper(id, b) &*& f <= 1;
{
    open [f]dispose_perm_helper(id, b);
    dispose_perm_unique(id);
    close [f]dispose_perm_helper(id, b);
}

predicate space_user(int id, real f) = 
    [_]ghost_cell<pair<int, int> >(id, ?info) &*&
    fraction_store_ticket<int, unit>(snd(info), f);

predicate space_user_info(int id; int count) = 
    [_]ghost_cell<pair<int, int> >(id, ?info) &*&
    fraction_store(snd(info), dispose_perm_helper, id, count, _);

lemma void space_user_info_create()
    requires true;
    ensures dispose_perm(?id) &*& space_user_info(id, 0);
{
    int id = create_ghost_cell(unit);
    int fsid = create_fraction_store_precursor(dispose_perm_helper);
    int sid = create_ghost_cell(pair(id, fsid));
    convert_fraction_store_precursor(fsid, dispose_perm_helper, sid);
    leak ghost_cell(sid, _);
    close dispose_perm(sid);
    close space_user_info(sid, 0);
}

lemma void space_user_info_zero(int id)
    requires dispose_perm(id) &*& space_user_info(id, ?count);
    ensures dispose_perm(id) &*& space_user_info(id, count) &*& count == 0;
{
    open space_user_info(id, count);
    assert [_]ghost_cell<pair<int, int> >(id, ?info);
    assert fraction_store(snd(info), dispose_perm_helper, id, _, _);
    close dispose_perm_helper(id, unit);
    produce_lemma_function_pointer_chunk(dispose_perm_helper_unique) 
        : predicate_unique<int, unit>(dispose_perm_helper)(arg1) { call(); } 
    {
        fraction_store_unique_empty<int, unit>(snd(info));
    }
    open dispose_perm_helper(id, _);
    close space_user_info(id, count);
}

lemma void space_user_info_dispose(int id)
    requires dispose_perm(id) &*& space_user_info(id, ?count);
    ensures count == 0;
{
    space_user_info_zero(id);
    open space_user_info(id, 0);
    assert [_]ghost_cell<pair<int, int> >(id, ?info);
    assert fraction_store(snd(info), dispose_perm_helper, id, _, _);
    fraction_store_dispose(snd(info));
    open dispose_perm(id);
    ghost_cell_leak(fst(info));
}

lemma void space_user_info_non_zero(int id)
    requires space_user(id, ?f) &*& space_user_info(id, ?count);
    ensures space_user(id, f) &*& space_user_info(id, count) &*& count > 0; 
{
    open space_user_info(id, count);
    open space_user(id, f);
    assert [_]ghost_cell<pair<int, int> >(id, ?info);
    fraction_store_ticket_info(snd(info), f);
    close space_user(id, f);
    close space_user_info(id, count);
}

lemma void space_user_info_add_user(int id, real f)
    requires [f]dispose_perm(id) &*& space_user_info(id, ?count);
    ensures space_user(id, f) &*& space_user_info(id, count + 1);
{
    open [f]dispose_perm(id);
    open space_user_info(id, count);
    assert [_]ghost_cell<pair<int, int> >(id, ?info);
    ghost_cell_fraction_info<unit>(fst(info));
    close [f]dispose_perm(id);
    fraction_store_deposit(snd(info), f);
    close space_user_info(id, count + 1);
    close space_user(id, f);
}


lemma void space_user_info_remove_user(int id, real f)
    requires space_user(id, f) &*& space_user_info(id, ?count);
    ensures [f]dispose_perm(id) &*& space_user_info(id, count - 1) &*& count > 0;
{
    open space_user(id, f);
    open space_user_info(id, count);
    assert [_]ghost_cell<pair<int, int> >(id, ?info);
    fraction_store_withdraw(snd(info), f);
    close space_user_info(id, count - 1);
}

@*/
