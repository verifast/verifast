/**
 * output-anything : I/O verification of a program that can print any character.
 *
 * This is interesting because we use a permission-based approach,
 * so the program must have a lot of permissions.
 *
 * In this case this is still finite, for a program that needs
 * an infinite amount of permissions, see output-any-string.c
 */
 

#include <stdio_simple.h>
//@ #include <bigstar.gh>

/*@
predicate_ctor output_helper(place t1, place t2)(char value) =
  write_char_io(t1, stdout, value, _, t2);

predicate output_anything(place t1, place t2) =
  bigstar(output_helper(t1, t2), nil);
@*/

int get_any_unsigned_char()
//@ requires true;
/*@ ensures
  // does not set the return value to a fixed value, but it's in bounds:
  result >= 0 && result <= 255;
@*/
{
  // implementation can be anything including constants and random generators.
  
  unsigned char c; // uninitialized, can be anything
  //@ produce_limits(c);  // ... but it's in bounds of the assumed architecture and compiler.
  return c;
}

int main() //@ : custom_main_spec
//@ requires token(?t1) &*& output_anything(t1, ?t2);
//@ ensures token(t2);
{
  
  int i;
  i = get_any_unsigned_char();
  
  //@ open output_anything(_, _);
  //@ bigstar_extract(output_helper(t1, t2), i);
  //@ open output_helper(t1, t2)(i);
  putchar(i);
  
  //@ leak bigstar(_, _);

  return 0;
}
