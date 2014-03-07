/**
 * stdio_simple.h - contracts for C standard input-output functions (simplified)
 * that allow you to specify input-output related properties.
 *
 * If you do not want to specify that, you can use the stdio.h.
 *
 * The specifications are for a simplified view on the stdio API:
 * - files cannot be opened/closed, only stdin/stdout/stderr is available
 * - reading and writing is not buffered and not read-ahead
 * - only putchar/getchar, no fread/fwrite
 * - functions are thread-safe (this is also the case in glibc).
 * 
 * To keep things useful, the following is taken into account:
 * - reading and writing can fail.
 */
 
#ifndef IO_STDIO_H
#define IO_STDIO_H
//@ #include <io.gh>
//@ #include <listex.gh>
//@ #include <assoclist.gh>
#include <stddef.h>


typedef struct file FILE;
struct file;

/*@
predicate read_char_io(time t1, FILE *file; unsigned char c, bool success, time t2);
predicate write_char_io(time t1, FILE *file, unsigned char c; bool success, time t2);
@*/

int getc(FILE *stream);
//@ requires read_char_io(?t1, stdin(), ?c, ?success, ?t2) &*& time(t1);
//@ ensures time(t2) &*& success ? result == c && c >= 0 && c <= 255 : result < 0;

int getchar();
//@ requires read_char_io(?t1, stdin(), ?c, ?success, ?t2) &*& time(t1);
//@ ensures time(t2) &*& success ? result == c && c >= 0 && c <= 255: result < 0;

int putchar(int c);
//@ requires write_char_io(?t1, stdout(), c, ?success, ?t2) &*& c >= 0 && c <= 255 &*& time(t1);
//@ ensures time(t2) &*& success ? result == c : result < 0;

int putc(int c, FILE *stream);
//@ requires write_char_io(?t1, stream, c, ?success, ?t2) &*& c >= 0 && c <= 255 &*& time(t1);
//@ ensures time(t2) &*& success ? result == c : result < 0;



/*@
fixpoint FILE* stderr();
fixpoint FILE* stdout();
fixpoint FILE* stdin();
@*/

FILE *get_stderr();
//@ requires true;
//@ ensures result == stderr();


// The author of the main function can provide a body of this predicate.
//@ predicate main_io(time t1, list<list<char> > commandline_arguments, time t2);
typedef int main_io/*@(int mainModule)@*/(int argc, char **argv);
  /*@ requires module(mainModule, true)
    &*& [_]argv(argv, argc, ?arguments)
    &*& main_io(?t1, arguments, ?t2)
    &*& time(t1);
  @*/
  /*@ ensures time(t2);
  @*/

#endif

