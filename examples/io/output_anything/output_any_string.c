/**
 * output-anything : I/O verification of a program that can print any string.
 *
 * This is interesting because we use a permission-based approach,
 * so we need to represent an infinite amount of permissions in the contract.
 */

#include <stdio_simple.h>
//#include <stdio.h>
//@ #include <bigstar.gh>

/*@
predicate write_string_io(place t1, list<char> string, place t2) =
  string == nil ?
    no_op(t1, t2)
  :
    write_char_io(t1, stdout, head(string), _, ?t_write)
    &*& write_string_io(t_write, tail(string), t2)
;
@*/

void write_string(char *string_arg)
//@ requires [?f]string(string_arg, ?str) &*& write_string_io(?t1, str, ?t2) &*& token(t1);
//@ ensures [f]string(string_arg, str) &*& token(t2);
{
  char *string_iterator = string_arg;
  //@ close exists(tail(str));
  //@ open [f]string(string_arg, str);  
  //@ open write_string_io(t1, str, t2);
  /*@
  if (str == nil){
    no_op();
  }
  @*/
  while(*string_iterator != 0)
  /*@ requires
    [f]character(string_iterator, ?c)
    &*& exists<list<char> >(?str_loop)
    &*& token(?t_loop)
    &*& c != 0 ?
      write_char_io(t_loop, stdout, c, _, ?t_write)
      &*& write_string_io(t_write, str_loop, t2)
      
      &*& [f]string(string_iterator + 1, str_loop)
    :
      t_loop == t2;
  @*/
  /*@ ensures
    [f]character(old_string_iterator, c)
    &*& token(t2)
    &*& c != 0 ?
      [f]string(old_string_iterator + 1, str_loop)
    :
      emp;
  @*/
  {
    //@ open exists(str_loop);
    //@ character_limits(string_iterator);
    putchar(*string_iterator);
    string_iterator++;
    //@ open [f]string(string_iterator, str_loop);

    //@ close exists(tail(str_loop));

    //@ open write_string_io(?t_sub, str_loop, t2);
    /*@
    if (str_loop == nil){
      no_op();
    }
    @*/
  }
}

/*@
predicate_ctor output_helper(place t1, place t2)(list<char> value) =
  write_string_io(t1, value, t2);

predicate output_anything(place t1, place t2) =
  bigstar(output_helper(t1, t2), nil);
@*/

char* get_any_string()
//@ requires true;
//@ ensures [_]string(result, _); // explicitly unspecified what the string is.
{
  return "Any finite string can be printed!\n";
}

int main() //@ : custom_main_spec
//@ requires token(?t1) &*& output_anything(t1, ?t2);
//@ ensures token(t2);
{
  char *string;
  string = get_any_string();
  
  //@ open output_anything(_, _);
  //@ assert [_]string(string, ?str);
  //@ bigstar_extract(output_helper(t1, t2), str);
  //@ open output_helper(t1, t2)(str);
  write_string(string);
  
  //@ leak bigstar(_, _);

  return 0;
}
