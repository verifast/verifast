//@ #include "../annotated_api/auxiliary_definitions.gh"

/*@

lemma void union_nil<t>(list<t> xs)
  requires true;
  ensures union(xs, nil) == xs && union(nil, xs) == xs;
{
  switch (xs)
  {
    case cons(x0, xs0):
      union_nil(xs0);
    case nil:
  }
}

lemma void union_subset<t>(list<t> xs, list<t> ys)
  requires subset(xs, ys) == true;
  ensures union(xs, ys) == ys;
{
  switch (xs)
  {
    case cons(x0, xs0):
      union_subset(xs0, ys);
    case nil:
      union_nil(ys);
  }
}

lemma void union_refl<t>(list<t> xs)
  requires true;
  ensures union(xs, xs) == xs;
{
  subset_refl(xs);
  union_subset(xs, xs);
}

lemma void forall_union<t>(list<t> xs, list<t> ys, fixpoint(t, bool) p)
  requires forall(xs, p) && forall(ys, p);
  ensures  true == forall(union(xs,ys), p);
{
  switch (xs)
  {
    case cons(x0, xs0):
      forall_union(xs0, ys, p);
    case nil:
      union_nil(ys);
  }
}

lemma void forall_subset<t>(list<t> xs, list<t> ys, fixpoint(t, bool) p)
  requires forall(ys, p) && subset(xs, ys);
  ensures  true == forall(xs, p);
{
  switch (xs)
  {
    case cons(x0, xs0):
      forall_subset(xs0, ys, p);
      mem_subset(x0, xs, ys);
      forall_mem(x0, ys, p);
    case nil:
  }
}

lemma void dummy_foreach_extract<t>(t x, list<t> xs)
  requires [_]dummy_foreach(xs, ?p) &*& mem(x, xs) == true;
  ensures [_]p(x);
{
  switch (xs)
  {
    case cons(x0, xs0):
      open [_]dummy_foreach(xs, p);
      if (x == x0) 
        assert [_]p(x);
      else
        dummy_foreach_extract<t>(x, xs0);
    case nil:
      assert false;
  }
}

lemma void dummy_foreach_union<t>(list<t> xs, list<t> ys)
  requires [_]dummy_foreach(xs, ?p) &*& [_]dummy_foreach(ys, p);
  ensures [_]dummy_foreach(union(xs, ys), p);
{
  switch (xs)
  {
    case cons(x0, xs0):
      open [_]dummy_foreach(xs, p);
      dummy_foreach_union(xs0, ys);
      if (!mem(x0, ys))
      {
        close dummy_foreach(union(xs, ys), p);
        leak dummy_foreach(union(xs, ys), p);
      }
    case nil:
      union_nil(ys);
  }
}

lemma void dummy_foreach_subset<t>(list<t> xs, list<t> ys)
  requires [_]dummy_foreach(ys, ?p) &*& true == subset(xs, ys);
  ensures [_]dummy_foreach(xs, p);
{
  switch (xs)
  {
    case cons(x0, xs0):
      dummy_foreach_subset(xs0, ys);
      dummy_foreach_extract(x0, ys);
      close dummy_foreach(xs, p);
      leak dummy_foreach(xs, p);
    case nil:
      close dummy_foreach(xs, p);
      leak dummy_foreach(xs, p);
  }
}

@*/
