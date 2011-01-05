#include "arrays.h"

/*@

lemma_auto void array_inv<t>()
    requires array<t>(?a, ?n, ?size, ?q, ?elems);
    ensures array<t>(a, n, size, q, elems) &*& 0 <= n &*& length(elems) == n;
{
    open array<t>(a, n, size, q, elems);
    if (n != 0)
        array_inv();
    close array<t>(a, n, size, q, elems);
}

lemma void array_split<t>(void *a, int offset)
    requires array<t>(a, ?n, ?size, ?q, ?as) &*& 0 <= offset &*& offset <= n;
    ensures array<t>(a, offset, size, q, take(offset, as)) &*& array<t>(a + (offset * size), n - offset, size, q, drop(offset, as));
{
  if (offset == 0) {
    take_0<t>(as);
    close array<t>(a, 0, size, q, nil);
  } else {
    open array<t>(a, n, size, q, as);
    array_split(a + size, offset - 1);
    close array<t>(a, offset, size, q, take(offset, as));
  }
}

lemma void array_merge<t>(void *a)
    requires array<t>(a, ?M, ?size, ?q, ?as) &*& array<t>(a + M * size, ?N, size, q, ?bs);
    ensures array<t>(a, M + N, size, q, append(as, bs));
{
    open array<t>(a, M, size, q, as);
    if (M != 0) {
        array_merge((char*) a + size);
        close array<t>(a, M + N, size, q, append(as, bs));
    }
}

lemma void array_unseparate_same<t>(void *a, list<t> xs)
    requires array<t>(a, ?M, ?size, ?q, take(M, xs)) &*& q(a + M * size, head(drop(M, xs))) &*& array<t>(a + (M *size) + size, ?N, size, q, tail(drop(M, xs))) &*& length(xs) == M + N + 1;
    ensures array<t>(a, M + N + 1, size, q, xs) &*& head(drop(M, xs)) == nth(M, xs);
{
    open array<t>(a, M, size, q, take(M, xs));
    switch (drop(M, xs)) { case nil: case cons(x0, xs0): }
    if (M != 0) {
        switch (xs) {
            case nil:
            case cons(h, t):
                array_unseparate_same(a + size, t);
                close array<t>(a, M + N + 1, size, q, xs);
        }
    }
    assert false;
}

lemma void array_unseparate<t>(void *a, int i, list<t> xs)
    requires array<t>(a, i, ?size, ?q, take(i, xs)) &*& q(a + i * size, ?y) &*& array<t>(a + (i + 1) * size, length(xs) - i - 1, size, q, tail(drop(i, xs)));
    ensures array<t>(a, length(xs), size, q, update(i, y, xs));
{
    open array<t>(a, i, size, q, take(i, xs));
    if (i == 0) {
        switch (xs) { case nil: case cons(x, xs0): }
    } else {
        switch (xs) { case nil: case cons(x, xs0): }
        array_unseparate(a + size, i - 1, tail(xs));
    }
    close array<t>(a, length(xs), size, q, update(i, y, xs));
}

@*/