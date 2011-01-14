#include "list.h"

/*@

lemma_auto void length_nonnegative<t>(list<t> xs)
    requires true;
    ensures 0 <= length(xs);
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
    switch(xs) {
      case nil: 
      case cons(h, t):
          length_append(t, ys);
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
            reverse_append(xs0, ys);
            append_assoc(reverse(ys), reverse(xs0), cons(x, nil));
    }
}

lemma void reverse_reverse<t>(list<t> xs)
    requires true;
    ensures reverse(reverse(xs)) == xs;
{
    switch (xs) {
        case nil:
        case cons(x, xs0):
            reverse_reverse(xs0);
            reverse_append(reverse(xs0), cons(x, nil));
    }
}

lemma void mem_nth<t>(int n, list<t> xs)
    requires 0 <= n &*& n < length(xs);
    ensures mem(nth(n, xs), xs) == true;
{
    switch (xs) {
        case nil:
        case cons(x, xs0):
            if (n != 0) {
                mem_nth(n - 1, xs0);
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

lemma void take_0<t>(list<t> xs)
    requires true;
    ensures take(0, xs) == nil;
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
                switch (xs0) {
                    case nil:
                    case cons(x0, xs1):
                }
            } else {
                drop_n_plus_one(n - 1, xs0);
            }
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

lemma void length_remove<t>(t x, list<t> xs)
    requires true;
    ensures length(remove(x, xs)) == (mem(x, xs) ?  length(xs) - 1 : length(xs));
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            if (x != x0)
                length_remove(x, xs0);
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
    requires 0 <= n &*& n <= length(xs);
    ensures length(drop(n, xs)) == length(xs) - n;
{
    switch (xs) {
        case nil:
        case cons(x, xs0):
            if (n != 0) {
                length_drop(n - 1, xs0);
            }
    }
}

lemma void length_take<a>(int n, list<a> xs)
    requires 0 <= n &*& n <= length(xs);
    ensures length(take(n, xs)) == n;
{
    switch (xs) {
        case nil:
        case cons(x, xs0):
            if (n != 0) {
                length_take(n - 1, xs0);
            }
    }
}

lemma void drop_n_take_n<a>(int n, list<a> xs)
    requires true;
    ensures drop(n, take(n, xs)) == nil;
{
    switch (xs) {
        case nil:
        case cons(x, xs0):
            drop_n_take_n(n - 1, xs0);
    }
}

lemma void nth_take<a>(int i, int n, list<a> xs)
    requires 0 <= i &*& i < n &*& n <= length(xs);
    ensures nth(i, take(n, xs)) == nth(i, xs);
{
    switch (xs) {
        case nil:
        case cons(x, xs0):
            if (i != 0) {
                nth_take(i - 1, n - 1, xs0);
            }
    }
}

lemma void drop_take_remove_nth<t>(list<t> xs, int n)
  requires 0<=n && n < length(xs);
  ensures append(take(n, xs), tail(drop(n, xs))) == remove_nth(n, xs);
{
  switch(xs) {
    case nil:
    case cons(h, t):
      if(n == 0) {
      } else {
        drop_take_remove_nth(t, n - 1);
      }
  }
}

lemma void mem_index_of<t>(t x, list<t> xs)
    requires mem(x, xs) == true;
    ensures 0 <= index_of(x, xs) && index_of(x, xs) < length(xs);
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            if (x != x0)
                mem_index_of(x, xs0);
    }
}

lemma void foreach_remove<t>(t x, list<t> xs)
    requires foreach(xs, ?p) &*& mem(x, xs) == true;
    ensures foreach(remove(x, xs), p) &*& p(x);
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            open foreach<t>(xs, p);
            if (x0 != x) {
                foreach_remove(x, xs0);
                close foreach<t>(remove(x, xs), p);
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
            if (x0 != x){
                open foreach<t>(remove(x, xs), p);
                foreach_unremove(x, xs0);
            }
            close foreach<t>(xs, p);
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

lemma void nth_update<t>(int i, int j, t y, list<t> xs)
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

lemma void length_update<t>(int i, t y, list<t> xs)
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

@*/