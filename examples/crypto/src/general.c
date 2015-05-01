#include "general.h"

#include "item.h"

void abort_crypto_lib(const char* message)
  //@ requires [?f]string(message, ?cs);
  //@ ensures  false;
{
  printf("An error has"); 
  printf("occurred while"); 
  printf("using the crypto"); 
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
    abort_crypto_lib("requested humongous malloc!!!!!!!!");

  void* result = malloc(size);
  if (result == 0)
    abort_crypto_lib("Malloc failed");

  return result;
}

void write_buffer(char **target, const char *source, int length)
  /*@ requires pointer(target, ?t) &*& chars(t, length, ?cs) &*&
               [?f]chars(source, length, ?cs0) &*&
               length > 0 &*& length <= INT_MAX &*&
               t + length <= (void*) UINTPTR_MAX;
  @*/
  /*@ ensures  pointer(target, t + length) &*& chars(t, length, cs0) &*&
               [f]chars(source, length, cs0);
  @*/
{
  memcpy(*target, source, (unsigned int) length);
  int l = (int) length;

  //@ open chars(t, length, cs0);
  //@ character_limits(t);
  *target = *target + l;
}

/*@

lemma void equal_append_chars_of_int(int i1, int i2, 
                                     list<char> cs1, list<char> cs2)
  requires INT_MIN <= i1 && i1 <= INT_MAX &*& INT_MIN <= i2 && i2 <= INT_MAX &*&
           append(chars_of_int(i1), cs1) == append(chars_of_int(i2), cs2);
  ensures  cs1 == cs2 &*& i1 == i2;
{
  drop_append(sizeof(int), chars_of_int(i1), cs1);
  drop_append(sizeof(int), chars_of_int(i2), cs2);
  take_append(sizeof(int), chars_of_int(i1), cs1);
  take_append(sizeof(int), chars_of_int(i2), cs2);
  chars_of_int_injective(i1, i2);
}

lemma void drop_drop(int i1, int i2, list<char> cs)
  requires i1 >= 0 &*& i2 >= 0 &*& i1 + i2 < length(cs);
  ensures  drop(i1, drop(i2, cs)) == drop(i1 + i2, cs);
{
  switch (cs)
  {
    case nil:
    case cons(x, xs0):
      if (i2 > 0)
      {
        drop_n_plus_one(i2, cs);
        drop_drop(i1, i2 - 1, xs0);
      }
  }
}

lemma void equal_list_equal_prefix(list<char> cs1, list<char> cs2, 
                                   list<char> cs3)
  requires append(cs1, cs3) == append(cs2, cs3);
  ensures  cs1 == cs2;
{
  switch (cs1)
  {
    case nil:
      length_append(cs2, cs3);
      switch (cs2)
      {
        case nil:
        case cons(x2, xs2):
      }
    case cons(x1, xs1):
      length_append(cs1, cs3);
      switch (cs2)
      {
        case nil: 
        case cons(x2, xs2): equal_list_equal_prefix(xs1, xs2, cs3);
      }
  }
}

lemma void equal_append(list<char> cs1, list<char> cs11, 
                        list<char> cs2, list<char> cs22)
  requires length(cs1) == length(cs2) &*&
           append(cs1, cs11) == append(cs2, cs22);
  ensures  cs1 == cs2 && cs11 == cs22;
{
  drop_append(length(cs1), cs1, cs11);
  drop_append(length(cs1), cs2, cs22);
  take_append(length(cs1), cs1, cs11);
  take_append(length(cs1), cs2, cs22);
}

lemma void equal_double_triple_append(
                              list<char> cs1, list<char> cs2, list<char> cs3,
                              list<char> cs4, list<char> cs5, list<char> cs6)
  requires true;
  ensures  append(cs1, append(cs2, append(cs3, append(cs4, append(cs5, cs6)))))
           == 
           append(append(cs1, append(cs2, cs3)),append(cs4, append(cs5, cs6)));
{
  append_assoc(cs1, append(cs2, cs3), append(cs4, append(cs5, cs6)));
  append_assoc(cs2, cs3, append(cs4, append(cs5, cs6)));
}

lemma void head_append<t>(list<t> xs, list<t> ys)
  requires length(xs) > 0;
  ensures head(xs) == head(append(xs, ys));
{
  switch(xs)
  {
    case cons(c, cs):
    case nil:
  }
}

lemma void head_mem<t>(list<t> l)
  requires length(l) > 0;
  ensures  true == mem(head(l), l);
{
  switch(l)
  {
    case cons(c, cs):
    case nil:
  }
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

lemma void length_equals_nat_length(list<char> cs)
  requires true;
  ensures  length(cs) == int_of_nat(nat_length(cs));
{
  switch(cs)
  {
    case cons(c0, cs0):
      length_equals_nat_length(cs0);
    case nil:
  }
}

@*/

