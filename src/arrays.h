#ifndef ARRAYS_H
#define ARRAYS_H

#include "listex.h"

/*@

predicate array<t>(void* a, int n, int elemsize, predicate(t*; t) q; list<t> elems) =
  n == 0 ?
    elems == nil
  :
    q(a, ?elem) &*& array<t>(((char*) a) + elemsize, n - 1, elemsize, q, ?elems0) &*& elems == cons(elem, elems0);

lemma_auto void array_inv<t>();
    requires array<t>(?a, ?n, ?size, ?q, ?elems);
    ensures array<t>(a, n, size, q, elems) &*& 0 <= n &*& length(elems) == n;

lemma void array_split<t>(void *a, int offset);
    requires array<t>(a, ?n, ?size, ?q, ?as) &*& 0 <= offset &*& offset <= n;
    ensures array<t>(a, offset, size, q, take(offset, as)) &*& array<t>(a + (offset * size), n - offset, size, q, drop(offset, as));

lemma void array_merge<t>(void *a);
    requires array<t>(a, ?M, ?size, ?q, ?as) &*& array<t>(a + M * size, ?N, size, q, ?bs);
    ensures array<t>(a, M + N, size, q, append(as, bs));

lemma void array_unseparate_same<t>(void *a, list<t> xs);
    requires array<t>(a, ?M, ?size, ?q, take(M, xs)) &*& q(a + M * size, head(drop(M, xs))) &*& array<t>(a + (M *size) + size, ?N, size, q, tail(drop(M, xs))) &*& length(xs) == M + N + 1;
    ensures array<t>(a, M + N + 1, size, q, xs) &*& head(drop(M, xs)) == nth(M, xs);

lemma void array_unseparate<t>(void *a, int i, list<t> xs);
    requires array<t>(a, i, ?size, ?q, take(i, xs)) &*& q(a + i * size, ?y) &*& array<t>(a + (i + 1) * size, length(xs) - i - 1, size, q, tail(drop(i, xs)));
    ensures array<t>(a, length(xs), size, q, update(i, y, xs));

@*/

#endif