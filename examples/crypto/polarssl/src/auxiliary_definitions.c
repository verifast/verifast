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
      assert union(xs, nil) == xs;
      assert union(nil, xs) == xs;
    case nil:
      assert union(xs, nil) == xs;
      assert union(nil, xs) == xs;
  }
}

lemma void subset_union<t>(list<t> xs, list<t> ys)
    requires subset(xs, ys) == true;
    ensures union(ys, xs) == ys;
{
  switch (xs)
  {
    case cons(x0, xs0):
      subset_union<t>(xs0, ys);
    case nil:
      union_nil(ys);
      assert union(xs, ys) == ys;
  }
}

lemma void union_refl<t>(list<t> xs)
    requires true;
    ensures union(xs, xs) == xs;
{
  subset_refl(xs);
  subset_union(xs, xs);
}

@*/
