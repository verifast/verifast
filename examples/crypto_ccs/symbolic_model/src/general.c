#include "general.h"

#include "item.h"

void abort_crypto_lib(const char* message)
  //@ requires [?f]string(message, ?cs);
  //@ ensures  false;
{
  printf("An error has ");
  printf("occurred while ");
  printf("using the crypto ");
  printf("library:\n\n\t");
  printf("%s\n\nAborting...\n", message);

  abort();
}

void *malloc_wrapper(int size)
  //@ requires 0 <= size;
  /*@ ensures  result != 0 &*&
               malloc_block(result, size) &*& chars(result, size, ?cs) &*&
               true == ((char *)0 < result &&
               result + size <= (char *)UINTPTR_MAX);
  @*/
{
  if (size > MAX_PACKAGE_SIZE)
    abort_crypto_lib("Requested humongous malloc!!!!!!!!");

  void* result = malloc(size);
  if (result == 0)
    abort_crypto_lib("Malloc failed");

  return result;
}

void write_buffer(char **target, const char *source, int length)
  /*@ requires pointer(target, ?t) &*& chars(t, length, ?cs) &*&
               [?f]crypto_chars(?kind, source, length, ?ccs0) &*&
               length > 0 &*& kind == normal ||
                 (kind == secret && length >= MINIMAL_STRING_SIZE)
               &*& length <= INT_MAX &*& t + length <= (void*) UINTPTR_MAX; @*/
  /*@ ensures  pointer(target, t + length) &*&
               crypto_chars(kind, t, length, ccs0) &*&
               [f]crypto_chars(kind, source, length, ccs0); @*/
{
  int l = (int) length;
  char *temp = *target;
  //@ open chars(t, length, cs);
  //@ character_limits(t);
  //@ close chars(t, length, cs);
  memcpy(*target, source, (unsigned int) length);
  *target = *target + l;
}

/*@

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

lemma void equal_append_chars_of_int(int i1, int i2,
                                     list<char> cs1, list<char> cs2)
  requires INT_MIN <= i1 && i1 <= INT_MAX &*& INT_MIN <= i2 && i2 <= INT_MAX &*&
           append(chars_of_int(i1), cs1) == append(chars_of_int(i2), cs2);
  ensures  cs1 == cs2 &*& i1 == i2;
{
  take_append(sizeof(int), chars_of_int(i1), cs1);
  take_append(sizeof(int), chars_of_int(i2), cs2);
  drop_append(sizeof(int), chars_of_int(i1), cs1);
  drop_append(sizeof(int), chars_of_int(i2), cs2);
  chars_of_int_injective(i1, i2);
}

lemma void equal_append_ccs_of_int(int i1, int i2, list<crypto_char> ccs1,
                                                   list<crypto_char> ccs2)
  requires INT_MIN <= i1 && i1 <= INT_MAX &*& INT_MIN <= i2 && i2 <= INT_MAX &*&
           append(ccs_of_int(i1), ccs1) == append(ccs_of_int(i2), ccs2);
  ensures  ccs1 == ccs2 &*& i1 == i2;
{
  cs_to_ccs_length(chars_of_int(i1));
  cs_to_ccs_length(chars_of_int(i2));
  take_append(sizeof(int), ccs_of_int(i1), ccs1);
  take_append(sizeof(int), ccs_of_int(i2), ccs2);
  drop_append(sizeof(int), ccs_of_int(i1), ccs1);
  drop_append(sizeof(int), ccs_of_int(i2), ccs2);
  chars_of_int_injective(i1, i2);
  cs_to_ccs_inj(chars_of_int(i1), chars_of_int(i2));
}

lemma void chars_of_unbounded_int_bounds(int i)
  requires true;
  ensures  INT_MIN <= i && i <= INT_MAX ?
             INT_MIN <= head(chars_of_unbounded_int(i)) &*&
             head(chars_of_unbounded_int(i)) <= INT_MAX
           :
             head(chars_of_unbounded_int(i)) == i;
{
  if (INT_MIN <= i && i <= INT_MAX)
  {
    assert length(chars_of_int(i)) == sizeof(int);
    head_mem(chars_of_int(i));
    chars_of_int_char_in_bounds(head(chars_of_int(i)), i);
  }
  else
  {
    assert head(chars_of_unbounded_int(i)) == i;
  }
}

lemma void repeat_length<T>(T t, nat n)
  requires true;
  ensures  nat_length(repeat(t, n)) == n;
{
  switch(n)
  {
    case succ(n0): repeat_length(t, n0);
    case zero:
  }
}

lemma void length_equals_nat_length<T>(list<T> xs)
  requires true;
  ensures  length(xs) == int_of_nat(nat_length(xs));
{
  switch(xs)
  {
    case cons(x0, xs0):
      length_equals_nat_length(xs0);
    case nil:
  }
}

lemma void int_of_nat_injective(nat n1, nat n2)
  requires int_of_nat(n1) == int_of_nat(n2);
  ensures  n1 == n2;
{
  switch(n1)
  {
    case succ(s1):
      switch(n2)
      {
        case succ(s2):
          int_of_nat_injective(s1, s2);
        case zero:
          assert false;
      }
    case zero:
      assert n1 == n2;
  }
}

@*/

