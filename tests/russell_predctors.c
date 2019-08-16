//@ #include <ghost_cells.gh>
//@ #include <quantifiers.gh>

/*@

inductive set = set(predicate(int) p);

predicate_ctor inj
    (fixpoint(set, bool) f) //~ should_fail
    (int id) =
    [1/2]ghost_cell<fixpoint(set, bool)>(id, f);

fixpoint bool Rbody(set s, fixpoint(set, bool) f) { return s != set(inj(f)) || !f(s); }

fixpoint bool R(fixpoint(fixpoint(fixpoint(set, bool), bool), bool) forall_f, set s) { return forall_f((Rbody)(s)); }

lemma void russell()
    requires true;
    ensures false;
{
    get_forall_t<fixpoint(set, bool)>();
    assert [_]is_forall_t(?forall_f);
    set setR = set(inj((R)(forall_f)));
    if (R(forall_f, setR)) {
        forall_t_elim(forall_f, (Rbody)(setR), (R)(forall_f));
    } else {
        ;
        fixpoint(set, bool) g = not_forall_t(forall_f, (Rbody)(setR));
        if (setR == set(inj(g))) {
            assert inj((R)(forall_f)) == inj(g);
            int id = create_ghost_cell<fixpoint(set, bool)>((R)(forall_f));
            close inj((R)(forall_f))(id);
            open inj(g)(id);
            assert (R)(forall_f) == g;
            assert !R(forall_f, setR);
        } else {
        }
    }
}
    
@*/
