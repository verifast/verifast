//@ #include <ghost_cells.gh>
//@ #include "ghost_cells_ex.gh"

/*@

predicate ghost_cell3(int id; int v1, int v2, int v3) = ghost_cell(id, pair(?v1_, pair(?v2_, ?v3_))) &*& v1 == v1_ &*& v2 == v2_ &*& v3 == v3_;

lemma int create_ghost_cell3(int v1, int v2, int v3)
    requires true;
    ensures ghost_cell3(result, v1, v2, v3);
{
    return create_ghost_cell(pair(v1, pair(v2, v3)));
}

@*/
