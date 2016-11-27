//@ #include "listex.gh"

/*@

lemma void take_plus_one<t>(int i, list<t> xs)
    requires 0 <= i &*& i < length(xs);
    ensures take(i + 1, xs) == append(take(i, xs), cons(nth(i, xs), nil));
{
    switch (xs) {
        case nil:
        case cons(x, xs0):
            if (i != 0) {
                take_plus_one(i - 1, xs0);
            }
    }
}

lemma void take_append<t>(int n, list<t> xs, list<t> ys)
  requires 0 <= n && n <= length(xs);
  ensures take(n, append(xs, ys)) == take(n, xs);
{
  switch(xs) {
    case nil:
    case cons(h, t):
      if(n == 0) {
      } else {
        take_append(n - 1, t, ys);
      }
  }
}

lemma void distinct_mem_nth_take<t>(list<t> xs, int i)
    requires distinct(xs) == true &*& 0 <= i &*& i < length(xs);
    ensures !mem(nth(i, xs), take(i, xs));
{
    switch (xs) {
        case nil:
        case cons(x, xs0):
            if (i != 0) {
                distinct_mem_nth_take(xs0, i - 1);
            }
    }
}

lemma void nth_drop<t>(int n, int k, list<t> xs)
    requires 0 <= n &*& 0 <= k &*& n + k < length(xs);
    ensures nth(n, drop(k, xs)) == nth(n + k, xs);
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            if (k != 0) {
                drop_n_plus_one(k, xs);
                nth_drop(n, k - 1, xs0);
            }
    }
}

lemma void neq_mem_remove<t>(t x, t y, list<t> xs)
    requires x != y;
    ensures mem(x, remove(y, xs)) == mem(x, xs);
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            neq_mem_remove(x, y, xs0);
    }
}

lemma void mem_remove_mem<t>(t x, t y, list<t> xs)
    requires mem(x, remove(y, xs)) == true;
    ensures mem(x, xs) == true;
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            if (x0 != x && x0 != y)
                mem_remove_mem(x, y, xs0);
    }
}

lemma void remove_commutes<t>(list<t> xs, t x, t y)
  requires true;
  ensures remove(x, remove(y, xs)) == remove(y, remove(x, xs));
{
  switch(xs) {
    case nil:
    case cons(h, t): remove_commutes(t, x, y);
  }
}

lemma void distinct_mem_remove<t>(t x, list<t> xs)
    requires distinct(xs) == true;
    ensures !mem(x, remove(x, xs));
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            distinct_mem_remove(x, xs0);
    }
}

lemma void distinct_remove<t>(t x, list<t> xs)
    requires distinct(xs) == true;
    ensures distinct(remove(x, xs)) == true;
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            if (x0 == x) {
            } else {
                distinct_remove(x, xs0);
                neq_mem_remove(x0, x, xs0);
            }
    }
}

lemma void mem_nth_index_of<t>(t x, list<t> xs)
    requires mem(x, xs) == true;
    ensures nth(index_of(x, xs), xs) == x;
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            if (x0 != x)
                mem_nth_index_of(x, xs0);
    }
}

lemma void index_of_append_l<t>(t x, list<t> xs, list<t> ys)
    requires mem(x, xs) == true;
    ensures index_of(x, append(xs, ys)) == index_of(x, xs);
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            if (x0 == x) {
            } else {
                index_of_append_l(x, xs0, ys);
            }
    }
}

lemma void index_of_append_r<t>(t x, list<t> xs, list<t> ys)
    requires !mem(x, xs);
    ensures index_of(x, append(xs, ys)) == length(xs) + index_of(x, ys);
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            index_of_append_r(x, xs0, ys);
    }
}

lemma void nth_index_of<t>(int i, list<t> xs)
  requires distinct(xs) == true &*& 0 <= i && i < length(xs);
  ensures index_of(nth(i, xs), xs) == i;
{
  switch(xs) {
    case nil:
    case cons(h, t):
      if(i != 0) {
      nth_index_of(i - 1, t);
      }
  }
}

lemma void map_append<a, b>(fixpoint(a, b) f, list<a> xs, list<a> ys)
    requires true;
    ensures map(f, append(xs, ys)) == append(map(f, xs), map(f, ys));
{
    switch (xs) {
        case nil:
        case cons(h, t):
            map_append(f, t, ys);
    }
}

lemma void mem_map<a, b>(a x, list<a> xs, fixpoint(a, b) f)
    requires mem(x, xs) == true;
    ensures mem(f(x), map(f, xs)) == true;
{
    switch (xs) {
        case nil:
        case cons(h, t):
            if (h == x) {
            } else {
                mem_map(x, t, f);
            }
    }
}

lemma void forall_append<t>(list<t> xs, list<t> ys, fixpoint(t, bool) p)
    requires true;
    ensures forall(append(xs, ys), p) == (forall(xs, p) && forall(ys, p));
{
    switch (xs) {
        case nil:
        case cons(x, xs0):
            forall_append(xs0, ys, p);
    }
}

lemma void forall_mem<t>(t x, list<t> xs, fixpoint(t, bool) p)
    requires forall(xs, p) == true &*& mem(x, xs) == true;
    ensures p(x) == true;
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            if (x0 != x)
                forall_mem(x, xs0, p);
    }
}

lemma void forall_drop<t>(list<t> xs, fixpoint(t, bool) p, int i)
    requires forall(xs, p) == true;
    ensures forall(drop(i, xs), p) == true;
{
    switch (xs) {
        case nil:
        case cons(x, xs0):
            forall_drop(xs0, p, i - 1);
    }
}

lemma void mem_max(int x, list<int> xs)
    requires true;
    ensures mem(max(x, xs), cons(x, xs)) == true;
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            if (x < x0) {
                mem_max(x0, xs0);
            } else {
                mem_max(x, xs0);
            }
    }
}

lemma void fold_left_append<a, b>(a x0, fixpoint(a, b, a) f, list<b> xs1, list<b> xs2)
    requires true;
    ensures fold_left(x0, f, append(xs1, xs2)) == fold_left(fold_left(x0, f, xs1), f, xs2);
{
    switch (xs1) {
        case nil:
        case cons(x, xs10):
            fold_left_append(f(x0, x), f, xs10, xs2);
    }
}

lemma void append_drop_take<t>(list<t> vs, int i)
  requires 0 <= i && i <= length(vs);
  ensures append(take(i, vs), drop(i, vs)) == vs;
{
  switch(vs) {
    case nil: 
    case cons(h, t):
      if(i == 0) {
      } else {
        append_drop_take(t, i - 1);
      }
  }
}

lemma void drop_append<t>(int n, list<t> xs, list<t> ys)
    requires length(xs) <= n;
    ensures drop(n, append(xs, ys)) == drop(n - length(xs), ys);
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            drop_append(n - 1, xs0, ys);
    }
}

lemma_auto void remove_all_nil<t>(list<t> xs)
    requires true;
    ensures remove_all(xs, nil) == nil;
{
    switch (xs) {
        case nil:
        case cons(x, xs0):
            remove_all_nil(xs0);
    }
}

lemma void remove_all_cons<t>(list<t> xs, t y, list<t> ys)
    requires !mem(y, xs);
    ensures remove_all(xs, cons(y, ys)) == cons(y, remove_all(xs, ys));
{
    switch (xs) {
        case nil:
        case cons(x, xs0):
            remove_all_cons(xs0, y, ys);
    }
}

lemma void mem_remove_all<t>(t x, list<t> xs, list<t> ys)
    requires mem(x, ys) == true &*& !mem(x, xs);
    ensures mem(x, remove_all(xs, ys)) == true;
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            mem_remove_all(x, xs0, ys);
            assert mem(x, remove_all(xs0, ys)) == true;
            neq_mem_remove(x, x0, remove_all(xs0, ys));
            assert mem(x, remove(x0, remove_all(xs0, ys))) == true;
            assert mem(x, remove_all(xs, ys)) == true;
    }
}

lemma void remove_commut<t>(t x1, t x2, list<t> xs)
    requires true;
    ensures remove(x1, remove(x2, xs)) == remove(x2, remove(x1, xs));
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            if (x1 == x2) {
            } else {
                if (x1 == x0) {
                } else if (x2 == x0) {
                } else {
                    remove_commut(x1, x2, xs0);
                }
            }
    }
}

lemma void remove_remove_all<t>(t x, list<t> xs, list<t> ys)
    requires true;
    ensures remove(x, remove_all(xs, ys)) == remove_all(xs, remove(x, ys));
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            remove_commut(x, x0, remove_all(xs0, ys));
            remove_remove_all(x, xs0, ys);
    }
}

lemma void subset_intersection<t>(list<t> xs, list<t> ys)
    requires subset(xs, ys) == true;
    ensures intersection(ys, xs) == xs;
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            subset_intersection(xs0, ys);
    }
}

lemma_auto void intersection_nil<t>(list<t> xs)
    requires true;
    ensures intersection(nil, xs) == nil;
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            intersection_nil(xs0);
    }
}

lemma void mem_intersection<t>(t x, list<t> xs, list<t> ys)
    requires true;
    ensures mem(x, intersection(xs, ys)) == (mem(x, xs) && mem(x, ys));
{
    switch (ys) {
        case nil:
        case cons(y0, ys0):
            mem_intersection(x, xs, ys0);
    }
}

lemma void mem_subset<t>(t x, list<t> xs, list<t> ys)
    requires mem(x, xs) == true &*& subset(xs, ys) == true;
    ensures mem(x, ys) == true;
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            if (x == x0) {
            } else {
                mem_subset(x, xs0, ys);
            }
    }
}

lemma void subset_trans<t>(list<t> xs, list<t> ys, list<t> zs)
    requires subset(xs, ys) == true &*& subset(ys, zs) == true;
    ensures subset(xs, zs) == true;
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            mem_subset(x0, ys, zs);
            subset_trans(xs0, ys, zs);
    }
}

lemma void subset_cons0<t>(list<t> xs, t y, list<t> ys)
    requires subset(xs, ys) == true;
    ensures subset(xs, cons(y, ys)) == true;
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            subset_cons0(xs0, y, ys);
    }
}

lemma_auto void subset_refl<t>(list<t> xs)
    requires true;
    ensures subset(xs, xs) == true;
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            subset_refl(xs0);
            subset_cons0(xs0, x0, xs0);
    }
}

lemma void subset_cons<t>(t x, list<t> xs)
    requires true;
    ensures subset(xs, cons(x, xs)) == true;
{
    subset_refl(xs);
    subset_cons0(xs, x, xs);
}

lemma void subset_remove<t>(t x, list<t> xs, list<t> ys)
    requires subset(xs, ys) == true;
    ensures subset(remove(x, xs), ys) == true;
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            if (x0 == x) {
            } else {
                subset_remove(x, xs0, ys);
            }
    }
}

lemma void subset_remove_all<t>(list<t> xs, list<t> ys)
    requires true;
    ensures subset(remove_all(xs, ys), ys) == true;
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            subset_remove_all(xs0, ys);
            subset_remove(x0, remove_all(xs0, ys), ys);
    }
}

lemma void not_mem_intersection<t>(t x, list<t> xs, list<t> ys)
    requires !mem(x, ys);
    ensures intersection(xs, ys) == intersection(remove(x, xs), ys);
{
    switch (ys) {
        case nil:
        case cons(y0, ys0):
            not_mem_intersection(x, xs, ys0);
            neq_mem_remove(y0, x, xs);
    }
}

lemma void not_mem_remove_eq<t>(t x, list<t> xs)
    requires !mem(x, xs);
    ensures remove(x, xs) == xs;
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            not_mem_remove_eq(x, xs0);
    }
}

lemma void remove_intersection<t>(t x, list<t> xs, list<t> ys)
    requires !mem(x, remove(x, intersection(xs, ys))) &*& !mem(x, remove(x, xs));
    ensures remove(x, intersection(xs, ys)) == intersection(remove(x, xs), ys);
{
    switch (ys) {
        case nil:
        case cons(y0, ys0):
            if (mem(y0, xs)) {
                if (y0 == x) {
                     assert remove(x, intersection(xs, ys)) == intersection(xs, ys0);
                     assert intersection(remove(x, xs), ys) == intersection(remove(x, xs), ys0);
                     not_mem_remove_eq(x, intersection(xs, ys0));
                     assert remove(x, intersection(xs, ys0)) == intersection(xs, ys0);
                     remove_intersection(x, xs, ys0);
                } else {
                     neq_mem_remove(y0, x, xs);
                     assert intersection(remove(x, xs), ys) == cons(y0, intersection(remove(x, xs), ys0));
                     remove_intersection(x, xs, ys0);
                }
            } else {
                if (y0 == x) {
                    remove_intersection(x, xs, ys0);
                } else {
                    neq_mem_remove(y0, x, xs);
                    remove_intersection(x, xs, ys0);
                }
            }
    }
}

lemma void subset_subset_intersection_subset<t>(list<t> xs, list<t> ys, list<t> zs)
    requires subset(xs, ys) == true &*& subset(xs, zs) == true;
    ensures subset(xs, intersection(ys, zs)) == true;
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            mem_intersection(x0, ys, zs);
            subset_subset_intersection_subset(xs0, ys, zs);
    }
}

lemma void subset_intersection_subset<t>(list<t> xs, list<t> ys)
    requires subset(xs, ys) == true;
    ensures subset(xs, intersection(xs, ys)) == true;
{
    subset_refl(xs);
    subset_subset_intersection_subset(xs, xs, ys);
}

lemma void foreach_remove_nth<t>(int n)
    requires [?f]foreach<t>(?xs, ?p) &*& 0 <= n &*& n < length(xs);
    ensures [f]foreach<t>(remove_nth(n, xs), p) &*& [f]p(nth(n, xs));
{
    open foreach(_, _);
    if (n != 0) {
        foreach_remove_nth(n - 1);
        close [f]foreach(remove_nth(n, xs), p);
    }
}

lemma void foreach_unremove_nth<t>(list<t> xs, int n)
    requires [?f]foreach<t>(remove_nth(n, xs), ?p) &*& [f]p(nth(n, xs)) &*& 0 <= n &*& n < length(xs);
    ensures [f]foreach(xs, p);
{
    assert xs == cons(?x, ?xs0);
    if (n != 0) {
        open foreach(_, _);
        foreach_unremove_nth(xs0, n - 1);
    }
    close [f]foreach(xs, p);
}

lemma void foreachp_remove<t>(t x, list<t> xs)
    requires foreachp(xs, ?p) &*& mem(x, xs) == true;
    ensures foreachp(remove(x, xs), p) &*& p(x);
{
  open foreachp(xs, p);
  switch(xs) {
    case nil:
    case cons(x0, xs0):
      if(x0 != x) {
        foreachp_remove(x, xs0);
        close foreachp(remove(x, xs), p);
      }
  }
}

lemma void foreachp_unremove<t>(t x, list<t> xs)
    requires foreachp(remove(x, xs), ?p) &*& mem(x, xs) == true &*& p(x);
    ensures foreachp(xs, p);
{
  open foreachp(remove(x, xs), p);
  switch(xs) {
    case nil:
    case cons(x0, xs0):
      if(x != x0) {
        foreachp_unremove(x, xs0);
      }
      close foreachp(xs, p);
  }
}

lemma void foreachp_remove_nth<t>(int n)
    requires foreachp<t>(?xs, ?p) &*& 0 <= n &*& n < length(xs);
    ensures foreachp<t>(remove_nth(n, xs), p) &*& p(nth(n, xs));
{
    open foreachp(_, _);
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            if (n == 0) {
            } else {
                foreachp_remove_nth(n - 1);
                close foreachp(remove_nth(n, xs), p);
            }
    }
}

lemma void foreachp_unremove_nth<t>(list<t> xs, int n)
    requires foreachp<t>(remove_nth(n, xs), ?p) &*& 0 <= n &*& n < length(xs) &*& p(nth(n, xs));
    ensures foreachp<t>(xs, p);
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            if (n == 0) {
            } else {
                open foreachp(_, _);
                foreachp_unremove_nth(xs0, n - 1);
            }
    }
}

@*/
