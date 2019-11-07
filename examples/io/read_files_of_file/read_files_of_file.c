/**
 * read-files-of-file.c -- read all files mentioned in a file
 *
 * Read a file "f", containing filenames. Reads
 * all these files and writes the contents to stdout.
 *
 * e.g. if the file "f" contains the contents "gh", then
 * the file g and h are read.
 *
 * An easy specification is to fix the order in which files
 * are opened, read, and written: read a filename from "f",
 * open that file, read one byte from that file, write that
 * one byte, etc. This would only allow one ordering of actions.
 *
 * To make it more interesting, we allow many orderings
 * instead of only one. However, we constrain that the output
 * is the concatenation of the input files.
 */

#include <stdio_simple.h>

/*@
predicate read_opened_file(place t1, FILE *f; list<char> text, place t_end) =
  read_char_io(t1, f, ?c, ?success, ?t2)
  // On paper, we write "c >= 0 ?" instead of "success ?" as a simplification.
  // They are equivalent because of the contract of fgetc and friends.
  &*& success ?
    read_opened_file(t2, f, ?sub_text, t_end)
    &*& text == cons(c, sub_text)
  :
    t_end == t2
    &*& text == nil;

predicate read_file(place t1, list<char> filename;
  list<unsigned char> text, place t_end) =
  
  fopen_io(t1, filename, {'r','b'}, ?file_handle, ?t2)
  &*& file_handle == 0 ?
    t_end == t2
    &*& text == nil
  :
    read_opened_file(t2, file_handle, text, ?t3)
    &*& fclose_io(t3, file_handle, t_end);

predicate write_opened_file(place t1, FILE *file_handle,
  list<unsigned char> text, place t_end) =
  
  text == nil ?
    no_op(t1, t_end)
  :
    write_char_io(t1, file_handle, head(text), _, ?t2)
    &*& write_opened_file(t2, file_handle, tail(text), t_end);

// Normally this would be "list<list<char > > filenames",
// and that works, but for similarity with the example on
// paper, we write "list<char> filenames" (one char per
// filename).
predicate read_files_io(place t1, list<char> filenames,
  list<char> text, place t_end) =
  
  filenames == nil ?
    // It's also possible to write "t_end==t1" here,
    // but it is better to write "no_op(t1, t_end)".
    // See the documentation of no_op in io.gh for more info.
    no_op(t1, t_end) &*& text == nil
  :
    read_file(t1, {head(filenames)}, ?text1, ?t2)
    &*& read_files_io(t2, tail(filenames), ?text2, t_end)
    &*& text == append(text1, text2);


predicate read_filename_list_io(place t1, FILE *stream; list<char>
  filenames, place t_end) =

  read_char_io(t1, stream, ?c, ?success, ?t2)
  &*& success ? // equivalent with "c >= 0"
    read_filename_list_io(t2, stream, ?sub_filenames, t_end)
    &*& c > 0 && c <= 127 ?
      filenames == cons(c, sub_filenames)
    :
      // null is not a valid filename, thus ignored.
      // Also ignore non 7bit ascii filenames.
      filenames == sub_filenames
  :
    t_end == t2
    &*& filenames == nil;

predicate read_file_of_files_io(place t1, list<char> filename,
  FILE *stream_out, place t_end) =
  
  fopen_io(t1, filename, {'r','b'}, ?meta_file, ?t2)
  &*& meta_file != 0 ?
    split(t2, ?t_meta, ?t_readwrite)
      &*& read_filename_list_io(t_meta, meta_file, ?filenames, ?t_meta2)
      &*& fclose_io(t_meta2, meta_file, ?t_meta3)
      // --
      &*& split(t_readwrite, ?t_read, ?t_write)
        &*& read_files_io(t_read, filenames, ?text, ?t_read2)
        //--
        &*& write_opened_file(t_write, stdout, text, ?t_write2)
      &*& join(t_read2, t_write2, ?t_readwrite2)
    &*& join(t_meta3, t_readwrite2, t_end)
  :
    t_end == t2;
@*/


// We choose the simplest implementation (alternatives would be buffering, threading, ...)

int main() //@ : custom_main_spec
//@ requires read_file_of_files_io(?t1, {'f'}, stdout, ?t_end) &*& token(t1);
//@ ensures token(t_end);
{
  
  //@ open read_file_of_files_io(_, _, _, _);
  //@ assert fopen_io(_, _, _, _, ?t2);
  FILE *meta = fopen("f", "rb");
  
  if (meta == 0){
    return 1;
  }
  
  int c = 0;
  //@ split_specific(t2);
  //@ split();
  //@ assert read_filename_list_io(_, _, _, ?t_read_list2); // bind t_read_list2
  //@ assert read_files_io(_, _, _, ?t_read2); // bind t_read2
  //@ assert write_opened_file(_, _, _, ?t_write2); // bind t_write2
  while (c >= 0)
    /*@ invariant
      stream(meta, {'r','b'})
      &*& c >= 0 ?
        read_filename_list_io(?t_cur, meta, ?filenames, t_read_list2) &*& token(t_cur)
        &*& read_files_io(?t_read, filenames, ?text, t_read2) &*& token(t_read)
        &*& write_opened_file(?t_write, stdout, text, t_write2) &*& token(t_write)
      :
        token(t_read_list2)
        &*& token(t_read2)
        &*& token(t_write2);
    @*/
  {
    //@ open read_filename_list_io(_, _, _, _);
    c = fgetc(meta);
    
    if (c > 0 && c < 128){
      char filename[2] = {};
      filename[0] = (char)c;
      
      //@ open read_files_io(_, _, _, _);
      //@ assert read_files_io(_, _, ?text_nextfiles, _);
      //@ open read_file(_, _, _, _);
      
      FILE *f = fopen(filename, "rb");
      if (f != 0){
        int c2 = 0;
        //@ assert read_opened_file(_, _, _, ?t_read_cur_end); // bind t_read_cur_end
        while (c2 >= 0)
        /*@ invariant
          stream(f, {'r','b'})
          &*& c2 >= 0 ?
            read_opened_file(?t_read_cur, f, ?text_onefile, t_read_cur_end) &*& token(t_read_cur)
            &*& write_opened_file(?t_write_cur, stdout, ?text_allfiles, t_write2) &*& token(t_write_cur)
            &*& append(text_onefile, text_nextfiles) == text_allfiles
          :
            token(t_read_cur_end)
            &*& write_opened_file(?t_write_cur, stdout, text_nextfiles, t_write2) &*& token(t_write_cur);
        @*/
        {
          //@ open read_opened_file(_, _, _, _);
          c2 = fgetc(f);
          if (c2 >= 0){
            //@ open write_opened_file(_, _, _, _);
            putchar(c2);
          }
        }
        fclose(f);
      }
      
    }
    
    /*@
    if (c < 0){
      open read_files_io(_, _, _, _);
      open write_opened_file(_, _, _, _);
      no_op();
      no_op();
    }
    @*/
  }
  
  fclose(meta);
  
  //@ join_specific(t_read2);
  //@ join();

  return 0;
}
