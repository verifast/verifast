//@ #include "auxiliary_definitions.gh"

/*@

lemma void union_nil<t>(list<t> xs)
  requires true;
  ensures  union_(xs, nil) == xs && union_(nil, xs) == xs;
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
  ensures  union_(xs, ys) == ys;
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
  ensures  union_(xs, xs) == xs;
{
  subset_refl(xs);
  union_subset(xs, xs);
}

lemma void forall_union<t>(list<t> xs, list<t> ys, fixpoint(t, bool) p)
  requires forall(xs, p) && forall(ys, p);
  ensures  true == forall(union_(xs,ys), p);
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
  ensures  [_]p(x);
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


lemma void dummy_foreach_singleton<t>(predicate(t) p, t x)
  requires [_]p(x);
  ensures  [_]dummy_foreach(cons(x, nil), p);
{
  close dummy_foreach(nil, p);
  leak dummy_foreach(nil, p);
  close dummy_foreach(cons(x, nil), p);
  leak dummy_foreach(cons(x, nil), p);
}

lemma void dummy_foreach_union<t>(list<t> xs, list<t> ys)
  requires [_]dummy_foreach(xs, ?p) &*& [_]dummy_foreach(ys, p);
  ensures  [_]dummy_foreach(union_(xs, ys), p);
{
  switch (xs)
  {
    case cons(x0, xs0):
      open [_]dummy_foreach(xs, p);
      dummy_foreach_union(xs0, ys);
      if (!mem(x0, ys))
      {
        close dummy_foreach(union_(xs, ys), p);
        leak dummy_foreach(union_(xs, ys), p);
      }
    case nil:
      union_nil(ys);
  }
}

lemma void dummy_foreach_subset<t>(list<t> xs, list<t> ys)
  requires [_]dummy_foreach(ys, ?p) &*& true == subset(xs, ys);
  ensures  [_]dummy_foreach(xs, p);
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


lemma void drop_drop<T>(int i1, int i2, list<T> xs)
  requires i1 >= 0 &*& i2 >= 0 &*& i1 + i2 < length(xs);
  ensures  drop(i1, drop(i2, xs)) == drop(i1 + i2, xs);
{
  switch (xs)
  {
    case nil:
    case cons(x0, xs0):
      if (i2 > 0)
      {
        drop_n_plus_one(i2, xs);
        drop_drop(i1, i2 - 1, xs0);
      }
  }
}

lemma void equal_list_equal_prefix<T>(list<T> xs1, list<T> xs2, list<T> xs3)
  requires append(xs1, xs3) == append(xs2, xs3);
  ensures  xs1 == xs2;
{
  switch (xs1)
  {
    case nil:
      length_append(xs2, xs3);
      switch (xs2)
      {
        case nil:
        case cons(x2', xs2'):
      }
    case cons(x1', xs1'):
      length_append(xs1, xs3);
      switch (xs2)
      {
        case nil:
        case cons(x2, xs2'): equal_list_equal_prefix(xs1', xs2', xs3);
      }
  }
}

lemma void equal_append<T>(list<T> xs1, list<T> xs11,
                           list<T> xs2, list<T> xs22)
  requires length(xs1) == length(xs2) &*&
           append(xs1, xs11) == append(xs2, xs22);
  ensures  xs1 == xs2 && xs11 == xs22;
{
  drop_append(length(xs1), xs1, xs11);
  drop_append(length(xs1), xs2, xs22);
  take_append(length(xs1), xs1, xs11);
  take_append(length(xs1), xs2, xs22);
}

lemma void equal_double_triple_append<T>(list<T> xs1, list<T> xs2, list<T> xs3,
                                         list<T> xs4, list<T> xs5, list<T> xs6)
  requires true;
  ensures  append(xs1, append(xs2, append(xs3, append(xs4, append(xs5, xs6)))))
           ==
           append(append(xs1, append(xs2, xs3)), append(xs4, append(xs5, xs6)));
{
  append_assoc(xs1, append(xs2, xs3), append(xs4, append(xs5, xs6)));
  append_assoc(xs2, xs3, append(xs4, append(xs5, xs6)));
}

lemma void head_append<T>(list<T> xs, list<T> ys)
  requires length(xs) > 0;
  ensures head(xs) == head(append(xs, ys));
{
  switch(xs)
  {
    case cons(c, cs):
    case nil:
  }
}

lemma void head_mem<T>(list<T> l)
  requires length(l) > 0;
  ensures  true == mem(head(l), l);
{
  switch(l)
  {
    case cons(c, cs):
    case nil:
  }
}

lemma void take_1<T>(list<T> xs)
  requires length(xs) > 0;
  ensures  take(1, xs) == cons(head(xs), nil);
{
  switch(xs)
  {
    case cons(c, cs):
    case nil:
  }
}

lemma void prefix_length<T>(list<T> xs, list<T> ys)
  requires true == prefix(xs, ys);
  ensures  length(xs) <= length(ys);
{
  switch(ys)
  {
    case cons(y0, ys0):
      switch(xs)
      {
        case cons(x0, xs0):
          prefix_length(xs0, ys0);
        case nil:
      }
    case nil:
  }
}

lemma void prefix_append<T>(list<T> xs, list<T> ys)
  requires true;
  ensures  true == prefix(xs, append(xs, ys));
{
  take_append(length(xs), xs, ys);
}

lemma void prefix_trans<T>(list<T> xs1, list<T> xs2, list<T> xs3)
  requires prefix(xs1, xs2) && prefix(xs2, xs3);
  ensures  true == prefix(xs1, xs3);
{
  switch(xs3)
  {
    case cons(x0, xs0):
      prefix_trans(drop(1, xs1), drop(1, xs2), xs0);
    case nil:
  }
}

lemma void sublist_refl<T>(list<T> xs)
  requires true;
  ensures  true == sublist(xs, xs);
{
  switch(xs)
  {
    case cons(x0, xs0):
    case nil:
  }
}

lemma void sublist_length<T>(list<T> xs, list<T> ys)
  requires true == sublist(xs, ys);
  ensures  length(xs) <= length(ys);
{
  switch(ys)
  {
    case cons(y0, ys0):
      if (prefix(xs, ys))
      {
        prefix_length(xs, ys);
      }
      else
      {
        sublist_length(xs, ys0);
      }
    case nil:
  }
}

lemma void sublist_append<T>(list<T> xs1, list<T> xs, list<T> xs2)
  requires true;
  ensures  true == sublist(xs, append(xs1, append(xs, xs2)));
{
  switch(xs1)
  {
    case cons(x10, xs10):
      list<T> xs_total = append(xs1, append(xs, xs2));
      if (false == prefix(xs, xs_total))
      {
        sublist_append(xs10, xs, xs2);
      }
    case nil:
      list<T> xs_total = append(xs1, append(xs, xs2));
      assert xs_total == append(xs, xs2);
      switch (xs_total)
      {
        case cons(x0, xs0):
          prefix_append(xs, xs2);
        case nil:
          switch (xs) {case cons(x0, xs0): case nil:}
      }
  }
}

lemma void sublist_trans<T>(list<T> xs1, list<T> xs2, list<T> xs3)
  requires sublist(xs1, xs2) && sublist(xs2, xs3);
  ensures  true == sublist(xs1, xs3);
{
  switch(xs3)
  {
    case cons(x30, xs30):
      switch(xs2)
      {
        case cons(x20, xs20):
          if (prefix(xs2, xs3))
          {
            if (prefix(xs1, xs2))
            {
              prefix_trans(xs1, xs2, xs3);
            }
            else
            {
              switch (xs30){case cons(x, xs): case nil:}
              sublist_trans(xs1, xs20, xs30);
            }
          }
          else
          {
            sublist_trans(xs1, xs2, xs30);
          }
        case nil:
      }
    case nil:
  }
}

lemma void take_length_bound<T>(int i, list<T> xs)
  requires i >= 0;
  ensures  length(take(i, xs)) <= i && length(take(i, xs)) <= length(xs);
{
  switch(xs)
  {
    case cons(x0, xs0):
      if (i > 0)
        take_length_bound<T>(i - 1, xs0);
    case nil:
  }
}

@*/
