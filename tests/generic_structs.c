#include <stdlib.h>

struct pair<A, B> {
  A fst;
  B snd;
};

struct pair<int, bool> *create_pair_int_bool(int fst, bool snd)
//@ requires true;
//@ ensures result->fst |-> fst &*& result->snd |-> snd &*& malloc_block_pair<int, bool>(result);
{
  struct pair<int, bool> *result = malloc(sizeof(struct pair<int, bool>));
  if (result == 0) abort();
  result->fst = fst;
  result->snd = snd;
  return result;
}

void dispose_pair_int_bool(struct pair<int, bool> *p)
//@ requires p->fst |-> _ &*& p->snd |-> _ &*& malloc_block_pair<int, bool>(p);
//@ ensures true;
{
  free(p);
}

void pair_int_bool_swap(struct pair<int, bool> *p1, struct pair<int, bool> *p2)
//@ requires p1->fst |-> ?fst1 &*& p1->snd |-> ?snd1 &*& p2->fst |-> ?fst2 &*& p2->snd |-> ?snd2;
//@ ensures p1->fst |-> fst2 &*& p1->snd |-> snd2 &*& p2->fst |-> fst1 &*& p2->snd |-> snd1;
{
  int tmp1 = p1->fst;
  bool tmp2 = p1->snd;
  p1->fst = p2->fst;
  p1->snd = p2->snd;
  p2->fst = tmp1;
  p2->snd = tmp2;
}

struct pair<T, U> *create_pair<T, U>(void *T_typeid, void *U_typeid, T fst, U snd)
//@ requires true;
//@ ensures result->fst |-> fst &*& result->snd |-> snd &*& malloc_block_pair<T, U>(result);
{
  struct pair<T, U> *result = malloc(sizeof(struct pair<T, U>));
  if (result == 0) abort();
  result->fst = fst;
  result->snd = snd;
  return result;
}

void dispose_pair<T, U>(void *T_typeid, void *U_typeid, struct pair<T, U> *p)
//@ requires p->fst |-> _ &*& p->snd |-> _ &*& malloc_block_pair<T, U>(p);
//@ ensures true;
{
  free(p);
}

void pair_swap<T, U>(void *T_typeid, void *U_typeid, struct pair<T, U> *p1, struct pair<T, U> *p2)
//@ requires p1->fst |-> ?fst1 &*& p1->snd |-> ?snd1 &*& p2->fst |-> ?fst2 &*& p2->snd |-> ?snd2;
//@ ensures p1->fst |-> fst2 &*& p1->snd |-> snd2 &*& p2->fst |-> fst1 &*& p2->snd |-> snd1;
{
  T tmp1 = p1->fst;
  U tmp2 = p1->snd;
  p1->fst = p2->fst;
  p1->snd = p2->snd;
  p2->fst = tmp1;
  p2->snd = tmp2;
}

struct pair<bool, int> pair_int_bool_flip(struct pair<int, bool> p)
//@ requires true;
//@ ensures result.fst == p.snd &*& result.snd == p.fst;
{
  struct pair<bool, int> result = {p.snd, p.fst};
  return result;
}

void pair_int_bool_flip_test()
//@ requires true;
//@ ensures true;
{
  struct pair<int, bool> myPair = {42, true};
  struct pair<bool, int> flippedPair = pair_int_bool_flip(myPair);
  assert(flippedPair.fst == true && flippedPair.snd == 42);
}

void testAddressTakenOrNot(struct pair<int, bool> p)
//@ requires p.fst == 42 && p.snd == true;
//@ ensures true;
{
  struct pair<int, bool> q = p;
  struct pair<int, bool> *q_ptr = &q;
  assert (q_ptr->fst == 42);
  assert (q_ptr->snd == true);
  struct pair<int, bool> r = q;
  assert(r.fst == 42);
  assert(r.snd == true);
}

struct pair<Y, X> pair_flip<X, Y>(struct pair<X, Y> p)
//@ requires true;
//@ ensures result.fst == p.snd &*& result.snd == p.fst;
{
  struct pair<Y, X> result = {p.snd, p.fst};
  return result;
}
