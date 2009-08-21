#ifndef GHOST_CELLS_H
#define GHOST_CELLS_H

/*@

predicate ghost_cell<t>(int id; t value);

lemma int create_ghost_cell<t>(t value);
    requires emp;
    ensures ghost_cell<t>(result, value);

lemma void ghost_cell_set_value<t>(int id, t value);
    requires ghost_cell<t>(id, _);
    ensures ghost_cell<t>(id, value);

@*/

#endif