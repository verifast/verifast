/**
 * output-anything : I/O verification of a program that can print any string.
 *
 * This is interesting because we use a permission-based approach,
 * so we need to represent an infinite amount of permissions in the contract.
 */

//@ #include <stdio_simple.h>
//#include <stdio.h>
//@ #include <bigstar.gh>

/*@
predicate write_string_io(time t1, list<char> string, time t2) =
  string == nil ?
    t1 == t2
  :
    write_char_io(t1, stdout, head(string), _, ?t_write)
    &*& write_string_io(t_write, tail(string), t2)
;
@*/

void write_string(char *string_arg)
//@ requires [?f]string(string_arg, ?str) &*& write_string_io(?t1, str, ?t2) &*& time(t1);
//@ ensures [f]string(string_arg, str) &*& time(t2);
{
  char *string_temp = string_arg;
  //@ close exists(tail(str));
  //@ open [f]string(string_arg, str);

  // Verifast currently, as far as I know, does not support a ghost else
  // branch for Tuerk-style loops (i.e. ghost code that gets symbolically
  // executed if the guard does not hold). As a result, the postcondition
  // must be a trivial consequence of the precondition if the guard does
  // not hold (because there is no support for writing ghost code that can transform it).
  // So, the precondition must contain more things, e.g. that
  // t_loop==t2 if c!=0. To make this more complex precondition hold, we need this open-close:
  //@ open write_string_io(t1, str, t2);
  //@ close write_string_io(t1, str, t2); 
  while(*string_temp != 0)
  /*@ requires
    [f]character(string_temp, ?c)
    &*& exists<list<char> >(?str_loop)
    &*& time(?t_loop)
    &*& write_string_io(t_loop, ?str_write, t2)
    &*& c != 0 ?
      [f]string(string_temp+1, str_loop)
      &*& str_write == cons(c, str_loop)
    :
      t_loop == t2
      &*& str_write == nil;
  @*/
  /*@ ensures
    [f]character(old_string_temp, c)
    &*& write_string_io(t2, nil, t2)
    &*& time(t2)
    &*& c != 0 ?
      [f]string(old_string_temp+1, str_loop)
    :
      emp;
  @*/
  {
    //@ open exists(str_loop);
    //@ open write_string_io(t_loop, str_write, t2);
    //@ character_limits(string_temp);
    putchar(*string_temp);
    string_temp++;
    //@ open [f]string(string_temp, str_loop);

    //@ close exists(tail(str_loop));

    //@ open write_string_io(?t_sub, tail(str_write), t2);
    //@ close write_string_io(t_sub, tail(str_write), t2); 
  }

  //@ open write_string_io(t2, nil, t2);
}

/*@
predicate_ctor output_helper(time t1, time t2)(list<char> value) =
  write_string_io(t1, value, t2);

predicate output_anything(time t1, time t2) =
  bigstar(output_helper(t1, t2), nil);
@*/

char* get_any_string()
//@ requires true;
//@ ensures [_]string(result, _); // explicitly unspecified what the string is.
{
  return "Any finite string can be printed!\n";
}

void main()
//@ requires time(?t1) &*& output_anything(t1, ?t2);
//@ ensures time(t2);
{
  char *string;
  string = get_any_string();
  
  //@ open output_anything(_, _);
  //@ assert [_]string(string, ?str);
  //@ bigstar_extract(output_helper(t1, t2), str);
  //@ open output_helper(t1, t2)(str);
  write_string(string);
  
  //@ leak bigstar(_, _);
}
