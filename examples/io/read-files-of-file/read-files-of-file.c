/**
 * read-filed-of-file.c -- read all files mentioned in a file
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

predicate read_opened_file(time t1, FILE *handle_in; list<char> contents, time t_end) =
  read_char_io(t1, handle_in, ?c, ?success, ?t2)
  &*& success ?
    read_opened_file(t2, handle_in, ?sub_contents, t_end)
    &*& contents == cons(c, sub_contents)
  :
    t_end == t2
    &*& contents == nil;

predicate read_file(time t1, list<char> filename; list<unsigned char> contents, time t_end) =
  fopen_io(t1, filename, {'r','b'}, ?file_handle, ?t2)
  &*& file_handle == 0 ?
    t_end == t2
    &*& contents == nil
  :
    read_opened_file(t2, file_handle, contents, ?t3)
    &*& fclose_io(t3, file_handle, t_end);

predicate write_opened_file(time t1, FILE *file_handle, list<unsigned char> contents; time t_end) =
  contents == nil ?
    t_end == t1
  :
    write_char_io(t1, file_handle, head(contents), _, ?t2)
    &*& write_opened_file(t2, file_handle, tail(contents), t_end);

predicate read_files_io(time t1, list<list<char> > filenames; list<char> contents, time t_end) =
  filenames == nil ?
    t_end == t1
    &*& contents == nil
  :
    read_file(t1, head(filenames), ?contents1, ?t2)
    &*& read_files_io(t2, tail(filenames), ?contents2, t_end)
    &*& contents == append(contents1, contents2);


predicate read_filename_list_io(time t1, FILE *stream; list<list<char> > filenames, time t_end) =
  read_char_io(t1, stream, ?c, ?success, ?t2)
  &*& success ?
    read_filename_list_io(t2, stream, ?sub_filenames, t_end)
    &*& c > 0 && c <= 127 ? // TODO
      filenames == cons({c}, sub_filenames)
    :
      // null is not a valid filename, thus ignored. Also ignore non 7bit ascii filenames.
      filenames == sub_filenames
  :
    t_end == t2
    &*& filenames == nil;

predicate read_file_of_files_io(time t1, list<char> filename, FILE *stream_out, time t_end) =
  fopen_io(t1, filename, {'r','b'}, ?meta_file, ?t2)
  &*& meta_file != 0 ?
    split(t2, ?t_read_list, ?t_readwrite)
      &*& read_filename_list_io(t_read_list, meta_file, ?filenames, ?t_read_list2)
      &*& fclose_io(t_read_list2, meta_file, ?t_read_list3)
      // --
      &*& split(t_readwrite, ?t_read, ?t_write)
        &*& read_files_io(t_read, filenames, ?contents, ?t_read2)
        //--
        &*& write_opened_file(t_write, stdout, contents, ?t_write2)
      &*& join(t_read2, t_write2, ?t_readwrite2)
    &*& join(t_read_list3, t_readwrite2, t_end)
  :
    t_end == t2;
@*/


// We choose the simplest implementation (alternatives would be buffering, threading, ...)

void main()
//@ requires read_file_of_files_io(?t1, {'f'}, stdout, ?t_end) &*& time(t1);
//@ ensures time(t_end);
{
  
  //@ open read_file_of_files_io(_, _, _, _);
  //@ assert fopen_io(_, _, _, _, ?t2);
  FILE *meta = fopen("f", "rb");
  
  if (meta == 0){
    return;
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
        read_filename_list_io(?t_cur, meta, ?filenames, t_read_list2) &*& time(t_cur)
        &*& read_files_io(?t_read, filenames, ?contents, t_read2) &*& time(t_read)
        &*& write_opened_file(?t_write, stdout, contents, t_write2) &*& time(t_write)
      :
        time(t_read_list2)
        &*& time(t_read2)
        &*& time(t_write2);
    @*/
  {
    //@ open read_filename_list_io(_, _, _, _);
    c = fgetc(meta);
    
    if (c > 0 && c < 128){
      char filename[2] = {};
      filename[0] = (char)c;
      
      //@ open read_files_io(_, _, _, _);
      //@ assert read_files_io(_, _, ?contents_nextfiles, _);
      //@ open read_file(_, _, _, _);
      
      FILE *f = fopen(filename, "rb");
      if (f != 0){
        int c2 = 0;
        //@ assert read_opened_file(_, _, _, ?t_read_cur_end); // bind t_read_cur_end
        while (c2 >= 0)
        /*@ invariant
          stream(f, {'r','b'})
          &*& c2 >= 0 ?
            read_opened_file(?t_read_cur, f, ?contents_onefile, t_read_cur_end) &*& time(t_read_cur)
            &*& write_opened_file(?t_write_cur, stdout, ?contents_allfiles, t_write2) &*& time(t_write_cur)
            &*& append(contents_onefile, contents_nextfiles) == contents_allfiles
          :
            time(t_read_cur_end)
            &*& write_opened_file(?t_write_cur, stdout, contents_nextfiles, t_write2) &*& time(t_write_cur);
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
    }
    @*/
  }
  
  fclose(meta);
  
  //@ join_specific(t_read2);
  //@ join();
}
