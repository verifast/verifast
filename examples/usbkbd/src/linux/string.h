#ifndef _LINUX_STRING_H
#define _LINUX_STRING_H

#include <linux/types.h>

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
 * Overlap is not allowed (source: "Unlike memcpy(), memmove() copes with overlapping areas." -- Linux's string.c)
 * 
 * It is unknown/unchecked whether copying 0 bytes is allowed, so the formal specs do not allow it
 * (note that, to be allowed, it must also work in the assembly implementations).
 * 
 */
// XXX return value.
void *memcpy(void *dest, const void *src, size_t count);
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


/**
 * strlcpy - Copy a %NUL terminated string into a sized buffer
 *
 * 
 * @dest: Where to copy the string to
 * @src: Where to copy the string from
 * @size: size of destination buffer
 *
 * Compatible with *BSD: the result is always a valid
 * NUL-terminated string that fits in the buffer (unless,
 * of course, the buffer size is zero). It does not pad
 * out the result like strncpy() does.
 *
 * (the above are the official specs)
 *
 */
size_t strlcpy(char * dest, const char * src, size_t size);
	/*@ requires
		// Based on the "unless, of course, the buffer size is zero" subsentence,
		// we conclude that size==0 is allowed.
		0 <= size
		
		&*& [?f]string(src, ?src_text)
		&*& chars(dest, size, ?dest_txt)
		
		// It is unclear whether we need precondition that dest contains '\0'
		// if 0 < size, so this is enforced in formal specs.
		// If this becomes clear, please state your sources. Please note that
		// it must be true for the assembly implementation as well.
		&*& size == 0 || mem('\0', dest_txt) == true
		;
	@*/
	//@ ensures [f]string(src, src_text) &*& chars(dest, size, ?new_dest_txt) &*& size == 0 || mem('\0', new_dest_txt) == true;

/**
 * strlcat - Append a length-limited, %NUL-terminated string to another
 * @dest: The string to be appended to
 * @src: The string to append to it
 * @count: The size of the destination buffer.
 *
 * (the above are the official specs)
 */
size_t strlcat(char* dest, const char * src, size_t count);
	/*@ requires
		// count==0 is not allowed because the string.c implementation writes to dest[0].
		0 < count
		
		&*& [?f]string(src, ?src_text)
		&*& chars(dest, count, ?old_dest_txt)
		&*& mem('\0', old_dest_txt) == true
		;
	@*/
	/*@ ensures
		[f]string(src, src_text)
		&*& chars(dest, count, ?new_dest_txt)
		&*& mem('\0', new_dest_txt) == true;
	@*/
  

size_t strlen(const char* s);
	//@ requires [?f]chars(s, ?count, ?text) &*& mem('\0', text) == true;
	//@ ensures [f]chars(s, count, text) &*& result == index_of('\0', text);
#endif