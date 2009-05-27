#ifndef GHOST_CELLS_H
#define GHOST_CELLS_H

/*@

predicate ghost_cell(int id; any value);

lemma int create_ghost_cell(any value);
    requires emp;
    ensures ghost_cell(result, value);

lemma void ghost_cell_set_value(int id, any value);
    requires ghost_cell(id, _);
    ensures ghost_cell(id, value);

@*/

#endif