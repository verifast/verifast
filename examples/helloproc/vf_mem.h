#ifndef VF_MEM_H
#define VF_MEM_H

/* Credits: vf_kmalloc* is based on VeriFast's malloc.h. */


//@ predicate vf_kmalloc_block(void *array, int size);


void vf_kfree(void *ptr);
	/*@ requires
		vf_kmalloc_block(ptr, ?size)
		&*& chars(ptr, ?cs)
		&*& length(cs) == size;
	@*/
	//@ ensures true;


/**
 * vf_kmalloc - allocate <size> bytes in kernel memory.
 *
 * It is allowed to malloc 0 bytes.
 */
void *vf_kmalloc(int size);
	//@ requires size >= 0;
	/*@ ensures
		result == 0 ?
			true
		:
			vf_kmalloc_block(result, size)
			&*& chars(result, ?chars)
			&*& length(chars) == size
		;
	@*/


/*@
fixpoint bool equals<t>(unit u, t x, t y){
	switch(u){
		case unit: return x == y;
	}
}
@*/


/**
 * vf_kzalloc - like vf_kmalloc but memory is zeroed.
 *
 * Zeroed memory is useful to make sure no kernelspace secrets leak to
 * userspace.
 */
void *vf_kzalloc(int size);
	//@ requires size >= 0;
	/*@ ensures
		result == 0 ?
			true
		:
			vf_kmalloc_block(result, size)
			&*& chars(result, ?chars)
			&*& length(chars) == size
			&*& forall(chars, (equals)(unit, '\0')) == true
		;
	@*/


/**
 * vf_memcpy - Copies count bytes from src to dest. 
 *
 * Overlap is not allowed.  Copying 0 bytes is not allowed.
 */
void vf_memcpy(void *dest, void *src, int count);
	/* Dissalowing overlap is enforced by chars(dest, ...)
	 * and [?frac]chars(src, ...), you can not have
	 * chars for the same memory location "twice".
	 */
	/*@ requires count > 0
		&*& [?frac]chars(src, ?srcList)
		&*& chars(dest, ?destList)
		&*& length(srcList) >= count
		&*& length(destList) >= count;
	@*/
	/*@ ensures
		[frac]chars(src, srcList)
		&*& chars(
			dest,
			append(take(count, srcList),
			drop(count, destList))
		);
	@*/


#endif /* VF_MEM_H */

