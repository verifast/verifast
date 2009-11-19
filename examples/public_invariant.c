struct cell {
  int x;
};

/*@ 
predicate cell(struct cell *c, int v) = c->x |-> v &*& 0 <= v;

predicate cell2<t>(struct cell *c, int v) = c->x |-> v &*& 0 <= v;

lemma_auto void cell_pos()
  requires [?f]cell(?c, ?v);
  ensures [f]cell(c, v) &*& 0 <= v;
{
  open [f]cell(c, v);
  close [f]cell(c, v);
}

@*/

void m(struct cell *c)
  //@ requires [?g]cell(c, ?v);
  //@ ensures [g]cell(c, v);
{
  //@ assert 0 <= v;
}