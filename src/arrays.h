#ifndef ARRAYS_H
#define ARRAYS_H

#include "listex.h"

/*@

predicate array<t>(void* a, int n, int elemsize, predicate(t*; t) q; list<t> elems) =
  n == 0 ?
    elems == nil
  :
    q(a, ?elem) &*& array<t>(a + elemsize, n - 1, elemsize, q, ?elems0) &*& elems == cons(elem, elems0);

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

predicate ints(int* a, int n; list<int> elems) = 
  array<int>(a, n, sizeof(int), integer, elems);

lemma_auto void ints_inv();
    requires ints(?a, ?n, ?elems);
    ensures ints(a, n, elems) &*& 0 <= n &*& length(elems) == n;

lemma void ints_split(int *array, int offset);
    requires ints(array, ?N, ?as) &*& 0 <= offset &*& offset <= N;
    ensures ints(array, offset, take(offset, as)) &*& ints(array + offset, N - offset, drop(offset, as));

lemma void ints_merge(int *a);
    requires ints(a, ?M, ?as) &*& ints(a + M, ?N, ?bs);
    ensures ints(a, M + N, append(as, bs));

lemma void ints_unseparate_same(int *array, list<int> xs);
    requires ints(array, ?M, take(M, xs)) &*& integer(array + M, head(drop(M, xs))) &*& ints(array + M + 1, ?N, tail(drop(M, xs))) &*& length(xs) == M + N + 1;
    ensures ints(array, M + N + 1, xs) &*& head(drop(M, xs)) == nth(M, xs);

lemma void ints_unseparate(int *array, int i, list<int> xs);
    requires ints(array, i, take(i, xs)) &*& integer(array + i, ?y) &*& ints(array + i + 1, length(xs) - i - 1, tail(drop(i, xs)));
    ensures ints(array, length(xs), update(i, y, xs));

@*/

#endif