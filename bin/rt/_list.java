/*@

lemma void length_nonnegative<t>(list<t> xs)
    requires true;
    ensures length(xs) >= 0;
{
    switch (xs) {
        case nil:
        case cons(x, xs0):
            length_nonnegative(xs0);
    }
}

lemma void append_nil<t>(list<t> xs)
    requires true;
    ensures append(xs, nil) == xs;
{
    switch (xs) {
        case nil:
        case cons(x, xs0):
            append_nil(xs0);
    }
}

lemma void append_assoc<t>(list<t> xs, list<t> ys, list<t> zs)
    requires true;
    ensures append(append(xs, ys), zs) == append(xs, append(ys, zs));
{
    switch (xs) {
        case nil:
        case cons(x, xs0):
            append_assoc(xs0, ys, zs);
    }
}

lemma void length_append<t>(list<t> xs, list<t> ys)
    requires true;
    ensures length(append(xs, ys)) == length(xs) + length(ys);
{
    switch (xs) {
        case nil:
        case cons(x, xs0):
            length_append(xs0, ys);
    }
}

lemma void reverse_append<t>(list<t> xs, list<t> ys)
    requires true;
    ensures reverse(append(xs, ys)) == append(reverse(ys), reverse(xs));
{
    switch (xs) {
        case nil:
            append_nil(reverse(ys));
        case cons(x, xs0):
            assert reverse(append(xs, ys)) == reverse(append(cons(x, xs0), ys));
            assert reverse(append(cons(x, xs0), ys)) == reverse(cons(x, append(xs0, ys)));
            assert reverse(cons(x, append(xs0, ys))) == append(reverse(append(xs0, ys)), cons(x, nil));
            reverse_append(xs0, ys);
            assert append(reverse(append(xs0, ys)), cons(x, nil)) == append(append(reverse(ys), reverse(xs0)), cons(x, nil));
            append_assoc(reverse(ys), reverse(xs0), cons(x, nil));
            assert append(append(reverse(ys), reverse(xs0)), cons(x, nil)) == append(reverse(ys), append(reverse(xs0), cons(x, nil)));
            assert append(reverse(ys), append(reverse(xs0), cons(x, nil))) == append(reverse(ys), reverse(xs));
    }
}

lemma void reverse_reverse<t>(list<t> xs)
    requires true;
    ensures reverse(reverse(xs)) == xs;
{
    switch (xs) {
        case nil:
        case cons(x, xs0):
            assert reverse(reverse(xs)) == reverse(reverse(cons(x, xs0)));
            assert reverse(reverse(cons(x, xs0))) == reverse(append(reverse(xs0), cons(x, nil)));
            reverse_append(reverse(xs0), cons(x, nil));
            assert reverse(append(reverse(xs0), cons(x, nil))) == append(cons(x, nil), reverse(reverse(xs0)));
            reverse_reverse(xs0);
    }
}

lemma void mem_nth<t>(int n, list<t> xs)
    requires 0 <= n && n < length(xs);
    ensures mem(nth(n, xs), xs) == true;
{
    switch (xs) {
        case nil:
        case cons(x, xs0):
            if (n == 0) {
            } else {
                mem_nth(n - 1, xs0);
            }
    }
}

lemma void nth_zero<t>(list<t> vs)
    requires true;
    ensures nth(0, vs) == head(vs);
{
    switch (vs) {
        case nil:
        case cons(v, vs0):
    }
}

lemma void mem_append<t>(list<t> xs, list<t> ys, t x)
    requires true;
    ensures mem(x, append(xs, ys)) == (mem(x, xs) || mem(x, ys));
{
  switch(xs) {
    case nil:
    case cons(h, t):
      mem_append(t, ys, x);
  }
}

lemma void take_0<t>(list<t> xs)
    requires true;
    ensures take(0, xs) == nil;
{
    switch (xs) {
        case nil:
        case cons(x, xs0):
    }
}

lemma void take_length<t>(list<t> xs)
    requires true;
    ensures take(length(xs), xs) == xs;
{
    switch (xs) {
        case nil:
        case cons(x, xs0):
            length_nonnegative(xs0);
            take_length(xs0);
    }
}

lemma void length_take<t>(int n, list<t> xs)
    requires 0 <= n && n <= length(xs);
    ensures length(take(n, xs)) == n;
{
    switch (xs) {
        case nil:
        case cons(x, xs0):
            if (n == 0) {
            } else {
                length_take(n - 1, xs0);
            }
    }
}

lemma void length_take_n<t>(int n, list<t> xs)
    requires 0 <= n && n <= length(xs);
    ensures length(take(n, xs)) == n;
{
    switch (xs) {
        case nil:
        case cons(x, xs0):
            if (n == 0) {
            } else {
                length_take(n - 1, xs0);
            }
    }
}

lemma void nth_take<t>(int i, int n, list<t> xs)
    requires 0 <= i && i < n && n <= length(xs);
    ensures nth(i, take(n, xs)) == nth(i, xs);
{
    switch (xs) {
        case nil:
        case cons(x, xs0):
            if (i == 0) {
            } else {
                nth_take(i - 1, n - 1, xs0);
            }
    }
}

lemma void drop_0<t>(list<t> xs)
    requires true;
    ensures drop(0, xs) == xs;
{
    switch (xs) {
        case nil:
        case cons(x, xs0):
    }
}

lemma void drop_n_plus_one<t>(int n, list<t> xs)
    requires 0 <= n &*& n < length(xs);
    ensures drop(n, xs) == cons(nth(n, xs), drop(n + 1, xs));
{
    switch (xs) {
        case nil:
        case cons(x, xs0):
            if (n == 0) {
                drop_0(xs0);
            } else {
                drop_n_plus_one(n - 1, xs0);
            }
    }
}

lemma void drop_length<t>(list<t> xs)
    requires true;
    ensures drop(length(xs), xs) == nil;
{
    switch (xs) {
        case nil:
        case cons(x, xs0):
            length_nonnegative(xs0);
            drop_length(xs0);
    }
}

lemma void length_drop<t>(int n, list<t> xs)
    requires 0 <= n && n <= length(xs);
    ensures length(drop(n, xs)) == length(xs) - n;
{
    switch (xs) {
        case nil:
        case cons(x, xs0):
            if (n == 0) {
            } else {
                length_drop(n - 1, xs0);
            }
    }
}

lemma void drop_n_take_n<t>(int n, list<t> xs)
    requires true;
    ensures drop(n, take(n, xs)) == nil;
{
    switch (xs) {
        case nil:
        case cons(x, xs0):
            if (n == 0) {
            } else {
                drop_n_take_n(n - 1, xs0);
            }
    }
}

lemma void append_take_drop<t>(int n, list<t> xs)
    requires 0 <= n && n < length(xs);
    ensures append(take(n, xs), drop(n, xs)) == xs;
{
    switch (xs) {
        case nil:
        case cons(x, xs0):
            if (n == 0) {
            } else {
                append_take_drop(n - 1, xs0);
            }
    }
}

lemma void nth_drop<t>(list<t> vs, int i)
    requires 0 <= i && i < length(vs);
    ensures nth(i, vs) == head(drop(i, vs));
{
    switch (vs) {
        case nil:
        case cons(v, vs0):
            if (i == 0) {
            } else {
                nth_drop(vs0, i - 1);
            }
    }
}

lemma void drop_take_remove_nth<t>(list<t> xs, int n)
    requires 0 <= n && n < length(xs);
    ensures append(take(n, xs), tail(drop(n, xs))) == remove_nth(n, xs);
{
    switch (xs) {
        case nil:
        case cons(x, xs0):
            if (n == 0) {
            } else {
                drop_take_remove_nth(xs0, n - 1);
            }
    }
}

lemma_auto void index_of_nonnegative<t>(t x, list<t> xs)
    requires true;
    ensures 0 <= index_of(x, xs);
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            if (x0 == x) {
            } else {
                index_of_nonnegative(x, xs0);
            }
    }
}

lemma void mem_index_of<t>(t x, list<t> xs)
    requires mem(x, xs) == true;
    ensures 0 <= index_of(x, xs) &*& index_of(x, xs) < length(xs);
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            if (x == x0) {
                length_nonnegative(xs0);
            } else {
                mem_index_of(x, xs0);
            }
    }
}

lemma void foreach_remove<t>(t x, list<t> xs)
    requires foreach(xs, ?p) &*& mem(x, xs) == true;
    ensures foreach(remove(x, xs), p) &*& p(x);
{
    open foreach(xs, p);
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            if (x == x0) {
            } else {
                foreach_remove(x, xs0);
                close foreach(remove(x, xs), p);
            }
    }
}

lemma void foreach_unremove<t>(t x, list<t> xs)
    requires foreach(remove(x, xs), ?p) &*& mem(x, xs) == true &*& p(x);
    ensures foreach(xs, p);
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            if (x == x0) {
                close foreach(xs, p);
            } else {
                open foreach(remove(x, xs), p);
                foreach_unremove(x, xs0);
                close foreach(xs, p);
            }
    }
}

lemma void foreach_append<t>(list<t> xs, list<t> ys)
    requires foreach(xs, ?p) &*& foreach(ys, p);
    ensures foreach(append(xs, ys), p);
{
    open foreach(xs, p);
    switch (xs) {
        case nil:
        case cons(x, xs0):
            foreach_append(xs0, ys);
            close foreach(append(xs, ys), p);
    }
}

lemma void foreachp_remove<t>(t x, list<t> xs)
    requires [?f]foreachp(xs, ?p) &*& mem(x, xs) == true;
    ensures [f]foreachp(remove(x, xs), p) &*& [f]p(x);
{
    open foreachp(xs, p);
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            if (x == x0) {
            } else {
                foreachp_remove(x, xs0);
                close [f]foreachp(remove(x, xs), p);
            }
    }
}

lemma void foreachp_unremove<t>(t x, list<t> xs)
    requires [?f]foreachp(remove(x, xs), ?p) &*& mem(x, xs) == true &*& [f]p(x);
    ensures [f]foreachp(xs, p);
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            if (x == x0) {
                close [f]foreachp(xs, p);
            } else {
                open foreachp(remove(x, xs), p);
                foreachp_unremove(x, xs0);
                close [f]foreachp(xs, p);
            }
    }
}

lemma void foreachp_append<t>(list<t> xs, list<t> ys)
    requires [?f]foreachp(xs, ?p) &*& [f]foreachp(ys, p);
    ensures [f]foreachp(append(xs, ys), p);
{
    open foreachp(xs, p);
    switch (xs) {
        case nil:
        case cons(x, xs0):
            foreachp_append(xs0, ys);
            close [f]foreachp(append(xs, ys), p);
    }
}

lemma void all_eq_append<t>(list<t> xs1, list<t> xs2, t x0)
    requires true;
    ensures all_eq(append(xs1, xs2), x0) == (all_eq(xs1, x0) && all_eq(xs2, x0));
{
    switch (xs1) {
        case nil:
        case cons(x, xs10):
            all_eq_append(xs10, xs2, x0);
    }
}

lemma void all_eq_drop<t>(int i, list<t> xs, t x0)
    requires all_eq(xs, x0) && 0 <= i && i <= length(xs);
    ensures all_eq(drop(i, xs), x0) == true;
{
  switch(xs) {
    case nil:
    case cons(h, t):
      if(i == 0) {
      } else {
        all_eq_drop(i - 1, t, x0);
      }
  }
}

lemma void all_eq_nth(list<int> xs, int i)
    requires all_eq(xs, 0) == true && 0 <= i && i < length(xs);
    ensures nth(i, xs) == 0;
{
    switch (xs) {
        case nil:
        case cons(x, xs0):
            if(i != 0) {
              all_eq_nth(xs0, i - 1);
            }
    }
}

lemma void drop_append<t>(list<t> xs1, list<t> xs2)
    requires true;
    ensures drop(length(xs1), append(xs1, xs2)) == xs2;
{
    switch (xs1) {
        case nil:
            drop_0(xs2);
        case cons(x, xs10):
            length_nonnegative(xs10);
            drop_append(xs10, xs2);
    }
}

lemma void foreach_remove_nth<t>(int i, list<t> xs)
    requires foreach(xs, ?p) &*& 0 <= i &*& i < length(xs);
    ensures p(nth<t>(i, xs)) &*& foreach(remove_nth<t>(i, xs), p);
{
	open foreach(xs, p);
	switch (xs) {
		case nil:
		case cons(x0, xs0):
			if (i == 0) {
			} else {
				foreach_remove_nth(i-1, xs0);
				close foreach(remove_nth(i, xs), p);
			}
	}
}

lemma void foreach_unremove_nth<t>(int i, list<t> xs)
    requires foreach(remove_nth<t>(i, xs), ?p) &*& p(nth<t>(i, xs));
    ensures foreach(xs, p);
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            if (i == 0) {
                close foreach(xs, p);
            } else {
                open foreach(remove_nth(i, xs), p);
                foreach_unremove_nth(i-1, xs0);
                close foreach(xs, p);
            }
    }
}

lemma void length_nul<t>(list<t> xs)
requires length(xs) == 0;
ensures xs == nil;
{
	switch (xs) {
		case nil:
		case cons(x0, xs0):
			length_nonnegative(xs0);
	}
}

lemma_auto(length(update(i, y, xs))) void length_update<t>(int i, t y, list<t> xs)
    requires true;
    ensures length(update(i, y, xs)) == length(xs);
{
  switch(xs) {
    case nil:
    case cons(h, t):
      if(i != 0) {
        length_update(i - 1, y, t);
      }
  }
}

lemma_auto(nth(i, update(j, y, xs))) void nth_update<t>(int i, int j, t y, list<t> xs)
    requires 0 <= i && i < length(xs) && 0 <= j && j < length(xs);
    ensures nth(i, update(j, y, xs)) == (i == j ? y : nth(i, xs));
{
  switch(xs) {
    case nil:
    case cons(h, t):
      if(j == 0) {
        if(i == 0) {
        } else {
        }
      } else {
        if(i == 0) {
        } else {
          nth_update<t>(i-1,j-1,y,t);
        }
      }
  }
}

lemma void append_take_nth_drop<t>(int i, list<t> xs)
  requires 0 <= i && i < length(xs);
  ensures xs == append(take(i, xs), cons(nth(i, xs), drop(i + 1, xs)));
{
  switch(xs) {
    case nil: 
    case cons(h, t):
      if(i == 0) {
        drop_0(t);
      } else {
        append_take_nth_drop<t>(i - 1 , t);
      }
  }
}

lemma void update_eq_append_cons_drop<t>(int i, t v, list<t> xs)
  requires 0 <= i && i < length(xs);
  ensures update(i, v, xs) == append(take(i, xs), cons(v, drop(i + 1, xs)));
{
  switch(xs) {
    case nil: 
    case cons(h, t):
      if(i == 0) {
        drop_0(t);
      } else {
        update_eq_append_cons_drop<t>(i - 1 , v, t);
      }
  }
}

lemma void take_one_more<t>(int i, list<t> xs)
  requires 0 <= i &*& i < length(xs);
  ensures take(i + 1, xs) == append(take(i, xs), cons(nth(i, xs), nil));
{
  switch(xs) {
    case nil:
    case cons(h, t):
      if(i == 0) {
        switch(t) { case nil: case cons(h0, t0): }
      } else {
        take_one_more(i - 1, t);
      }
  }
}

lemma void take_update<t>(t v, int i, list<t> xs, int j)
  requires 0 <= i && i < length(xs) && 0 <= j && j <= i;
  ensures take(j, xs) == take(j, update(i, v, xs));
{
  switch(xs) {
    case nil:
    case cons(h, t):
      if(i == 0) {
        
      } else {
        if (j == 0) {
        } else {
          take_update(v, i - 1, t, j - 1);
        }
      }
  }
}

lemma void remove_remove_nth<t>(t x, list<t> xs)
    requires true;
    ensures remove(x, xs) == remove_nth(index_of(x, xs), xs);
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            if (x0 == x) {
            } else {
                remove_remove_nth(x, xs0);
            }
    }
}

lemma void index_of_nth<t>(int i, list<t> xs)
    requires 0 <= i &*& i < length(xs);
    ensures index_of(nth(i, xs), xs) <= i;
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            if (i == 0) {
            } else {
                index_of_nth(i - 1, xs0);
            }
    }
}

lemma void nth_index_of<t>(t x, list<t> xs)
    requires index_of(x, xs) < length(xs);
    ensures nth(index_of(x, xs), xs) == x;
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            if (x0 == x) {
            } else {
                nth_index_of(x, xs0);
            }
    }
}

lemma void mem_remove_eq<t>(t x, list<t> xs)
    requires true;
    ensures !mem(x, xs) == (remove(x, xs) == xs);
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            mem_remove_eq(x, xs0);
    }
}

lemma void forall_append<t>(list<t> xs, list<t> ys, fixpoint(t, boolean) p)
    requires true;
    ensures forall(append(xs, ys), p) == (forall(xs, p) && forall(ys, p));
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            forall_append(xs0, ys, p);
    }
}

lemma_auto void drop_drop<t>(int m, int n, list<t> xs)
    requires 0 <= m && 0 <= n && m + n <= length(xs);
    ensures drop(m, drop(n, xs)) == drop(m + n, xs);
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            if (n == 0) {
            } else {
                drop_drop(m, n - 1, xs0);
            }
    }
}

lemma_auto void nth_append_left<t>(int n, list<t> xs, list<t> ys)
    requires 0 <= n && n < length(xs);
    ensures nth(n, append(xs, ys)) == nth(n, xs);
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            if (n == 0) {
            } else {
                nth_append_left(n - 1, xs0, ys);
            }
    }
}

lemma_auto void nth_append_right<t>(int n, list<t> xs, list<t> ys)
    requires length(xs) <= n;
    ensures nth(n, append(xs, ys)) == nth(n - length(xs), ys);
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            nth_append_right(n - 1, xs0, ys);
            length_nonnegative(xs0);
    }
}

lemma void remove_nth_take_drop<t>(list<t> xs, int n)
    requires 0 <= n && n < length(xs);
    ensures remove_nth(n, xs) == append(take(n, xs), drop(n + 1, xs));
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            if (n == 0) {
                drop_0(xs0);
            } else {
                remove_nth_take_drop(xs0, n - 1);
            }
    }
}

lemma_auto void nth_drop0<t>(int n, int m, list<t> xs)
    requires 0 <= n && 0 <= m;
    ensures nth(n, drop(m, xs)) == nth(n + m, xs);
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            if (m == 0) {
            } else {
                nth_drop0(n, m - 1, xs0);
            }
    }
}

@*/