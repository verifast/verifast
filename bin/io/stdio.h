/**
 * io/stdio.h - contracts for C standard input-output functions
 * that allow you to specify input-output related properties.
 *
 * If you do not want to specify that, you can use the stdio.h in
 * the ../ directory.
 */
 
#ifndef IO_STDIO_H
#define IO_STDIO_H
//@ #include <io/io.gh>
//@ #include <listex.gh>
//@ #include <assoclist.gh>
#include <stddef.h>

typedef struct file FILE;
struct file;
/*@
predicate file(FILE *fp, fopen_mode mode);
@*/

/*@
inductive fopen_seek_mode = fopen_truncate | fopen_append | fopen_begin;
inductive fopen_mode = fopen_mode(bool read, bool write, fopen_seek_mode);
@*/

/*@
fixpoint list<pair<list<char>, fopen_mode> > fopen_modes(){
  return {
    pair({'r'    ,'b'}, fopen_mode(true , false, fopen_begin   ) ),
    pair({'r','+','b'}, fopen_mode(true , true , fopen_begin   ) ),
    pair({'w'    ,'b'}, fopen_mode(false, true , fopen_truncate) ),
    pair({'w','+','b'}, fopen_mode(true , true , fopen_truncate) ),
    pair({'a'    ,'b'}, fopen_mode(false, true , fopen_append  ) ),
    pair({'a','+','b'}, fopen_mode(true , true , fopen_append  ) )
  };
}
@*/
/**
 * Parses fopen mode string like "rw+".
 *
 * We currently only support binary mode, non-binary mode has different
 * behaviour across operating systems and is a source of errors and
 * incompatibilities.
 */
/*@
fixpoint fopen_mode parse_fopen_mode(list<char> string){
  return assoc(string, fopen_modes());
}
fixpoint bool is_valid_fopen_mode(list<char> string){
  return mem_assoc(fopen_modes(), string);
}
@*/

/**
 * fopen - open a file.
 *
 * Assumption: fopen can be called concurrently with everything (including itself).
 */
//@ predicate fopen_io(time t1, list<char> filename, fopen_mode mode, FILE *file, time t2);
FILE* fopen(char* filename, char* mode);
/*@ requires [?f]string(filename, ?fcs) &*& [?g]string(mode, ?mcs)
             &*& true==is_valid_fopen_mode(mcs)
             &*& fopen_io(?t1, fcs, parse_fopen_mode(mcs), ?file, ?t2)
             &*& time(t1);
@*/
/*@ ensures [f]string(filename, fcs) &*& [g]string(mode, mcs)
            &*& time(t2)
            &*& result == file
            &*& file != 0 ?
              file(result, parse_fopen_mode(mcs))
            :
              emp;
@*/



/**
 * fwrite - write a file.
 *
 * fwrite can be called concurrently with everything (including itself).
 * Note that other processes might also write to the file.
 */
//@ predicate fwrite_atomic_io(time t1, FILE *file, char c, bool success, time t2);
/*@ predicate fwrite_io(time t1, FILE *file, list<char> to_write, size_t prophecy_bytes_written, time t2) =
  to_write == nil ?
    t1 == t2 && prophecy_bytes_written == 0
  :
    fwrite_atomic_io(t1, file, head(to_write), ?success, ?t_between)
    &*& success == true ?
      fwrite_io(t_between, file, tail(to_write), prophecy_bytes_written - 1, t2)
    :
      prophecy_bytes_written == 0;
@*/
size_t fwrite(void* buffer, size_t size, size_t n, FILE* fp);
/*@ requires
  n >= 0 && size >= 0
  &*& [?f]file(fp, ?file_mode)
  &*& file_mode == fopen_mode(_, true, _)
  &*& n == 0 || size == 0?
    emp
  :
    [?fc]chars(buffer, ?m, ?cs)
    &*& size * n <= m
    &*& fwrite_io(?t1, fp, take(size*n, cs), ?prophecy_bytes_written, ?t2)
    &*& time(t1)
    &*& ensures
      [fc]chars(buffer, m, cs)
      &*& time(t2)
      &*& prophecy_bytes_written <= size*n && prophecy_bytes_written >= 0
      &*& prophecy_bytes_written != 0 ?
        // fwrite tries to write <n> times <size> bytes.
        // If this fails, the result might be that the last chunk
        // of <size> bytes is only written partially (this is experimentally confirmed
        // on Linux 3.2.0 with tmpfs).
        // At least <result>*<size> bytes are written, but 
        // there might be more if <n>!=1.
        exists<int>(?remainder)
        &*& result * size + remainder == prophecy_bytes_written
      :
        result <= 0
    ;
@*/
//@ ensures [f]file(fp, file_mode); // most of postcondition embedded above.


/**
 * fread - Like fwrite but for reading -- see fwrite.
 */
//@ predicate fread_atomic_io(time t1, FILE *file, char c, bool success, time t2);
/*@ predicate fread_io(time t1, FILE *file, int size_requested, list<char> prophecy_read, time t2) =
  size_requested == 0 ?
    t1 == t2 && prophecy_read == nil
  :
    fread_atomic_io(t1, file, ?c, ?success, ?t_between)
    &*& success == true ?
      c == head(prophecy_read)
      &*& fread_io(t_between, file, size_requested - 1, tail(prophecy_read), t2)
    :
      prophecy_read == nil;
@*/
size_t fread(void* buffer, size_t size, size_t n, FILE* fp);
/*@ requires
  n >= 0 && size >= 0
  &*& [?f]file(fp, ?file_mode)
  &*& file_mode == fopen_mode(true, _, _)
  &*& n == 0 || size == 0 ?
    emp
  :
    chars(buffer, ?m, ?cs)
    &*& size * n <= m
    &*& fread_io(?t1, fp, size*n, ?prophecy_read, ?t2)
    &*& time(t1)
    &*& ensures
      chars(buffer, m, ?cs_new)
      &*& time(t2)
      &*& length(prophecy_read) <= size*n
      &*& prophecy_read != nil ?
        take(length(prophecy_read), cs_new) == prophecy_read
        &*& exists<int>(?remainder)
        &*& result * size + remainder == length(prophecy_read)
      :
        result <= 0
    ;
@*/
//@ ensures [f]file(fp, file_mode);

//@ predicate fclose_io(time t1, FILE *file, time t2);
int fclose(FILE* fp); 
//@ requires file(fp, ?mode) &*& fclose_io(?t1, fp, ?t2) &*& time(t1);
//@ ensures time(t2);

/**
 * get_stdin() - similar to "stdin".
 *
 * "stdin" is an "extern", which is unsupported by VeriFast.
 * For now you can use get_stdin() instead.
 */
//@ predicate is_stdin(FILE *fp);
FILE* get_stdin();
//@ requires [_]is_stdin(?fp);
//@ ensures is_stdin(fp) &*& result == fp;

//@ predicate is_stdout(FILE *fp);
FILE* get_stdout();
//@ requires [_]is_stdout(?fp);
//@ ensures result == fp;


#endif

