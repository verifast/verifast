/** 
 * An approach for APIs that do the buffering themselves.
 * 
 * Consider an API that provides a function to buffered_write,
 * but the write does not actually happen when called.
 * Instead, it is put in a buffer. The write can then
 * happen any later time the buffered_write function is called.
 * The API provides a flush function that forces that
 * all pending writes also happen.
 * This is what C standard libraries like glibc do:
 * fwrite() and putchar() do not always do a system call,
 * they might postpone it to a future write() call.
 *
 * How to write the specifications of this buffered_write function
 * and of the flush function? How to verify the implemention?
 * How to use it?
 *
 * This file implements on approach for dealing with this:
 * the contract of buffered_write says "I might write some pending
 * data and some data you gave me, but i do not tell
 * how much of it". Still, the contract guarantees that
 * all writes happen in correct order. The flush contracts
 * says that all pending writes are done.
 */
//@ #include <io.gh>

/*--------------------- SYSCALL ---------------------*/
/*@
predicate syscall_putchar_io(place t1, int c, place t2);
@*/
void syscall_putchar(int c);
//@ requires token(?t1) &*& syscall_putchar_io(t1, c, ?t2);
//@ ensures token(t2);

/*@
predicate syscall_write_io(place t1, list<int> string, place t2) =
  string == nil ?
    no_op(t1, t2)
  :
    syscall_putchar_io(t1, head(string), ?t_between)
    &*& syscall_write_io(t1, tail(string), t2);
@*/


/*--------------------- STDLIB ---------------------*/
struct stdlib{
  int *buffer;
  int buffer_size;
  int buffer_used;
};
/*@
inductive stdlib_state = stdlib_state(list<int> to_write, place t1, place t2);
predicate stdlib(struct stdlib *stdlib, place t1, place t2) =
  stdlib->buffer |-> ?buffer
  &*& stdlib->buffer_size |-> ?buffer_size
  &*& stdlib->buffer_used |-> ?buffer_used
  //&*& ints(buffer, buffer_used, to_write)
  //&*& ints(buffer + buffer_used, buffer_size - buffer_used, _);
  &*& integer(buffer, ?i)
  &*& buffer_size == 1 ?
    syscall_putchar_io(t1, i, t2)
  :
    buffer_size == 0
    // this is not a no_op; stdlib does not represent
    // a regular i/o action. Instead it contains the
    // set of postponed I/O actions (because of buffering),
    // which can be the empty set. In that case, t1==t2.
    &*& t1 == t2
;

predicate stdlib_putchars_io(place t1, list<int> string, place t2) =
  string == nil ?
    no_op(t1, t2)
  :
    syscall_putchar_io(t1, head(string), ?t_between)
    &*& stdlib_putchars_io(t_between, tail(string), t2)
;


predicate stdlib_putchar_io(place t1, int c, place t2) =
  syscall_putchar_io(t1, c, t2);
@*/


void stdlib_putchar(struct stdlib *stdlib, int c)
/*@ requires token(?t1) &*& stdlib(stdlib, t1, ?t_postponed)
  &*& stdlib_putchar_io(t_postponed, c, ?t2);
@*/
/*@ ensures stdlib(stdlib, ?t1_new, t2)
  &*& token(t1_new);
@*/
{
  //@ open stdlib(stdlib, _, _);
  //@ open stdlib_putchar_io(_, _, _);
  if (stdlib->buffer_size == 1){
    syscall_putchar(*stdlib->buffer);
    
    syscall_putchar(c);
    stdlib->buffer_size = 0;
    //@ close stdlib(stdlib, t2, t2);
  }else{
    *stdlib->buffer = c;
    stdlib->buffer_size = 1;
    //@ close stdlib(stdlib, t1, t2);
  }	
}

void stdlib_flush_stdout(struct stdlib *stdlib)
/*@ requires token(?t1) &*& stdlib(stdlib, t1, ?t_postponed);
@*/
/*@ ensures stdlib(stdlib, t_postponed, t_postponed)
  &*& token(t_postponed);
@*/
{
  //@ open stdlib(stdlib, _, _);
  if (stdlib->buffer_size == 1){
    syscall_putchar(*stdlib->buffer);
    stdlib->buffer_size = 0; 
  }
  //@ close stdlib(stdlib, t_postponed, t_postponed);
}

/*--------------------- USER -----------------------*/

typedef int my_main_spec(struct stdlib *stdlib);
/*@ requires token(?t1)
  &*& stdlib(stdlib, t1, t1)
  &*& stdlib_putchar_io(t1, 'h', ?t2)
  &*& stdlib_putchar_io(t2, 'i', ?t3);
@*/
/*@
  ensures token(t3) &*& stdlib(stdlib, t3, t3);
@*/

int main(struct stdlib *stdlib) //@ : my_main_spec
/*@ requires token(?t1)
  &*& stdlib(stdlib, t1, t1)
  &*& stdlib_putchar_io(t1, 'h', ?t2)
  &*& stdlib_putchar_io(t2, 'i', ?t3);
@*/
/*@
  ensures token(t3) &*& stdlib(stdlib, t3, t3);
@*/
{
  stdlib_putchar(stdlib, 'h');
  stdlib_putchar(stdlib, 'i');
  stdlib_flush_stdout(stdlib);

  return 0;
}

