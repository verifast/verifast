#include "listex.h"

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

lemma void length_remove(int x, list<int> xs)
    requires mem(x, xs) == true;
    ensures length(remove(x, xs)) == length(xs) - 1;
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            if (x != x0)
                length_remove(x, xs0);
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

lemma void nth_update<t>(int i, int j, t y, list<t> xs)
    requires 0 <= i &*& i < length(xs) &*& 0 <= j &*& j < length(xs);
    ensures nth(i, update(j, y, xs)) == (i == j ? y : nth(i, xs));
{
    switch (xs) {
        case nil:
        case cons(x, xs0):
            if (i != 0 && j != 0)
                nth_update(i - 1, j - 1, y, xs0);
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

@*/