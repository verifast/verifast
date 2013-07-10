#ifndef _LINUX_STRING_H
#define _LINUX_STRING_H

#include "linux+types.h"

void *memscan(void *addr, int c, __kernel_size_t size);
/*@ requires
	// Allow starting earlier than addr argument for convenience of caller.
	[?f]chars(?start_addr, ?length, ?cs)
	&*& start_addr <= addr
	&*& length >= size + ((void*)addr - (void*)start_addr)
	
	// The int being searched might be bigger than 1 byte,
	// (but according to string.c's implementation,
	// the returned value doesn't have to be aligned on
	// int's size boundaries).
	&*& size >= sizeof(int);
@*/
//@ ensures [f]chars(start_addr, length, cs);

/**
 * memcpy - Copies count bytes from src to dest. 
 *
 * Overlap is not allowed.  Copying 0 bytes is not allowed.
 */
// XXX return value.
void *memcpy(void *dest, /*const*/ void *src, size_t count);
	/* Dissalowing overlap is enforced by chars(dest, ...)
	 * and [?frac]chars(src, ...), you can not have
	 * chars for the same memory location "twice".
	 */
	/*@ requires count > 0
		&*& [?f]chars(src,?length_src_list,?src_list)
		&*& chars(dest,?length_dest_list,?dest_list)
		&*& length_src_list >= count
		&*& length_dest_list >= count;
	@*/
	/*@ ensures
		[f]chars(src,length_src_list,src_list)
		
		&*& chars(dest, length_dest_list, 
			append(
				take(count, src_list),
				drop(count, dest_list)
			)	
		);
	@*/

// need precondition that dest contains '\0' if count > 0?
size_t strlcpy(char * dest, const char * src, size_t count);
  //@ requires 0 <= count &*& [?f]string(src, ?src_text) &*& chars(dest, count, ?dest_txt);
  //@ ensures [f]string(src, src_text) &*& chars(dest, count, ?new_dest_txt) &*& count == 0 || mem('\0', new_dest_txt) == true;

size_t strlcat(char* dest, const char * src, size_t count);
  //@ requires 0 <= count &*& [?f]string(src, ?src_text) &*& chars(dest, count, ?old_dest_txt);
  //@ ensures [f]string(src, src_text) &*& chars(dest, count, ?new_dest_txt) &*& count == 0 || !mem('\0', old_dest_txt) || mem('\0', new_dest_txt) == true;
  
size_t strlen(const char* s);
  //@ requires chars(s, ?count, ?text) &*& mem('\0', text) == true;
  //@ ensures chars(s, count, text) &*& result == index_of('\0', text);
#endif