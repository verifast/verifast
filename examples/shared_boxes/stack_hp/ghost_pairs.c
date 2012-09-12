//@ #include "ghost_pairs.gh"
//@ #include "ghost_cells.gh"


/*
    A ghost object that represents a pair of values.
    The implementation illustrates how gcell's can be used to model fields of a struct.
     
*/

/*@
predicate ghost_pair(int id;) = 
    [1/3]ghost_cell<pair<int,pair<int,int> > >(id, ?fields) &*&
    ghost_cell<bool>(snd(snd(fields)), true); //dummy gcell to get fraction info lemma

predicate ghost_pair_fst<t>(int id; t v)=
    [1/3]ghost_cell<pair<int,pair<int,int> > >(id, ?fields) &*&
    ghost_cell(fst(fields), v);
    
predicate ghost_pair_snd<t>(int id; t v)=
    [1/3]ghost_cell<pair<int,pair<int,int> > >(id, ?fields) &*&
    ghost_cell(fst(snd(fields)), v);

lemma int create_ghost_pair<t1,t2>(t1 v1, t2 v2)
    requires true;
    ensures ghost_pair(result) &*& ghost_pair_fst<t1>(result, v1)  &*& ghost_pair_snd<t2>(result, v2);
{
    int did = create_ghost_cell(true);
    int fid = create_ghost_cell(v1);
    int sid = create_ghost_cell(v2);
    int id = create_ghost_cell(pair(fid, pair(sid, did)));
    close ghost_pair(id);
    close ghost_pair_fst(id, v1);
    close ghost_pair_snd(id, v2);
    return id;
}
lemma void ghost_pair_set_fst<t>(int id, t v)
    requires ghost_pair_fst<t>(id, _);
    ensures ghost_pair_fst<t>(id, v);
{
    open ghost_pair_fst(id, _);
    assert [1/3]ghost_cell<pair<int, pair<int,int> > >(id, ?fields);
    ghost_cell_mutate(fst(fields), v);
    close ghost_pair_fst(id, v);
}
lemma void ghost_pair_set_snd<t>(int id, t v)
    requires ghost_pair_snd<t>(id, _);
    ensures ghost_pair_snd<t>(id, v);
{
    open ghost_pair_snd(id, _);
    assert [1/3]ghost_cell<pair<int, pair<int,int> > >(id, ?fields);
    ghost_cell_mutate(fst(snd(fields)), v);
    close ghost_pair_snd(id, v);
}
lemma void dispose_ghost_pair<t1,t2>(int id)
    requires ghost_pair(id) &*& ghost_pair_fst<t1>(id, _)  &*& ghost_pair_snd<t2>(id, _);
    ensures true;
{
    open ghost_pair(id); open ghost_pair_fst<t1>(id, _); open ghost_pair_snd<t2>(id, _);
    assert ghost_cell<pair<int, pair<int,int> > >(id, ?fields);
    ghost_cell_leak<pair<int, pair<int,int> > >(id);
    ghost_cell_leak<t1>(fst(fields));
    ghost_cell_leak<t2>(fst(snd(fields)));
    ghost_cell_leak<bool>(snd(snd(fields)));
}

lemma void ghost_pair_fraction_info<t>(int id)
    requires [?f]ghost_pair(id);
    ensures [f]ghost_pair(id) &*& 0 < f &*& f <= 1;
{
    open [f]ghost_pair(id);
    assert [f/3]ghost_cell<pair<int, pair<int,int> > >(id, ?fields);
    ghost_cell_fraction_info(snd(snd(fields)));
    close [f]ghost_pair(id);
}
lemma void ghost_pair_fst_fraction_info<t>(int id)
    requires [?f]ghost_pair_fst<t>(id, ?value);
    ensures [f]ghost_pair_fst<t>(id, value) &*& 0 < f &*& f <= 1;
{
    open [f]ghost_pair_fst<t>(id, value);
    assert [f/3]ghost_cell<pair<int, pair<int,int> > >(id, ?fields);
    ghost_cell_fraction_info(fst(fields));
    close [f]ghost_pair_fst<t>(id, value);
}
lemma void ghost_pair_snd_fraction_info<t>(int id)
    requires [?f]ghost_pair_snd<t>(id, ?value);
    ensures [f]ghost_pair_snd<t>(id, value) &*& 0 < f &*& f <= 1;
{
    open [f]ghost_pair_snd<t>(id, value);
    assert [f/3]ghost_cell<pair<int, pair<int,int> > >(id, ?fields);
    ghost_cell_fraction_info(fst(snd(fields)));
    close [f]ghost_pair_snd<t>(id, value);
}
@*/