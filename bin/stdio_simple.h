/**
 * stdio_simple.h - contracts for C standard input-output functions (simplified)
 * that allow you to specify input-output related properties.
 *
 * If you do not want to specify that, you can use the stdio.h.
 *
 * The specifications are for a simplified view on the stdio API:
 * - limited mode for fopen/fclose
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
predicate read_char_io(place t1, FILE *file; int c, bool success, place t2);
predicate write_char_io(place t1, FILE *file, unsigned char c; bool success, place t2);
@*/

/*@
fixpoint FILE* get_stderr();
fixpoint FILE* get_stdout();
fixpoint FILE* get_stdin();
@*/

#define stderr (get_stderr())
#define stdout (get_stdout())
#define stdin (get_stdin())

FILE *get_stderr();
//@ requires true;
//@ ensures result == stderr;

int fgetc(FILE *stream);
/*@ requires read_char_io(?t1, stream, ?c, ?success, ?t2) &*& token(t1)
  &*& stream != stdin ?
    [?f]stream(stream, ?mode) &*& true==does_fopen_mode_allow_reading(mode)
    &*& ensures
      [f]stream(stream, mode)
      &*& token(t2) &*& result == c &*& (success ? c >= 0 && c <= 255 : c < 0)
  : 
    // no stream required for stdin for convenience.
    ensures
      token(t2) &*& result == c &*& (success ? c >= 0 && c <= 255 : c < 0);
@*/
/*@ ensures emp; // ensures clauses embedded in requires clause.
@*/

#define getc(stream) fgetc(stream)

int getchar();
//@ requires read_char_io(?t1, stdin, ?c, ?success, ?t2) &*& token(t1);
//@ ensures token(t2) &*& result == c &*& success ? c >= 0 && c <= 255: result < 0;

/**
 * The character c "cast to an unsigned char" (source: man putchar(3)) is written.
 * This conversion to an unsigned char is always defined (see C99 sec. 6.3.1.3).
 */
int putchar(int c);
//@ requires write_char_io(?t1, stdout, c, ?success, ?t2) &*& token(t1);
//@ ensures token(t2) &*& success ? result == c : result < 0;

int fputc(int c, FILE *stream);
/*@ requires write_char_io(?t1, stream, c, ?success, ?t2) &*& token(t1)
  &*& true==(stream != stdout && stream != stderr) ?
    [?f]stream(stream, ?mode) &*& true==does_fopen_mode_allow_writing(mode)
    &*& ensures
      [f]stream(stream, mode)
      &*& token(t2) &*& (success ? result == c : result < 0)
    :
      ensures
      token(t2) &*& (success ? result == c : result < 0);
@*/
//@ ensures emp; // ensures clauses embedded in requires clause.

#define putc(c, stream) fputc(c, stream)

/*@
fixpoint bool is_valid_fopen_mode(list<char> mode_str){
  return mode_str == {'r','b'} || mode_str == {'w','b'}; // currently not supporting much.
}

fixpoint bool does_fopen_mode_allow_writing(list<char> mode_str){
  return mode_str == {'w','b'}; 
}

fixpoint bool does_fopen_mode_allow_reading(list<char> mode_str){
  return mode_str == {'r','b'}; 
}
@*/

//@ predicate stream(FILE *stream, list<char> mode);

//@ predicate fopen_io(place t1, list<char> filename, list<char> mode; FILE *stream, place t2);
FILE *fopen(char *filename, char *mode);
/*@ requires [?ff]string(filename, ?filename_str) &*& [?fm]string(mode, ?mode_str)
  &*& true==is_valid_fopen_mode(mode_str)
  &*& fopen_io(?t1, filename_str, mode_str, ?stream, ?t2) &*& token(t1);
@*/
/*@ ensures
  [ff]string(filename, filename_str)
  &*& [fm]string(mode, mode_str)
  &*& result == stream
  &*& token(t2)
  &*& stream != 0 ?
    stream(result, mode_str)
  :
    emp;
@*/

//@ predicate fclose_io(place t1, FILE *stream; place t2);
void fclose(FILE *stream);
/*@ requires stream(stream, _) &*& fclose_io(?t1, stream, ?t2) &*& token(t1); @*/
/*@ ensures token(t2); @*/


// The author of the main function can provide a body of this predicate.
//@ predicate main_io(place t1, list<list<char> > commandline_arguments, place t2);
typedef int main_io/*@(int mainModule)@*/(int argc, char **argv);
  /*@ requires module(mainModule, true)
    &*& [_]argv(argv, argc, ?arguments)
    &*& main_io(?t1, arguments, ?t2)
    &*& token(t1);
  @*/
  /*@ ensures token(t2);
  @*/

#endif

