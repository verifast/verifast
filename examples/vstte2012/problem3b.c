#include "malloc.h"
#include "arrays.h"
#include "listex.h"

/*
Terminology: if the array is STUFF1_empty_STUFF2, then bighead = stuff2, bigtail == stuff1.
*/

struct ring_buffer{
	int *fields; // buffer contents
	int size;
	int first; // start counting with 0
	int len;
};

/*@

predicate ring_buffer(struct ring_buffer *buffer, int size, list<int> items) =
	size >= 0 && size * 4 < INT_MAX
	
	&*& buffer->fields |-> ?fields
	&*& buffer->size |-> size
	&*& buffer->first |-> ?first
	&*& buffer->len |-> ?len
	&*& first >= 0 && first < size
	&*& length(items) == len
	&*& len <= size  
	
	&*& malloc_block(fields, 4 * size)
	&*& malloc_block_ring_buffer(buffer)
	&*& array<int>(fields, size, sizeof(int), integer, ?elems)
	&*& items == take(len,append(drop(first, elems), take(first, elems)))
	;
	
@*/

struct ring_buffer *ring_buffer_create(int size)
//@ requires size >= 1 &*& size * sizeof(int) < INT_MAX;
/*@ ensures
	result == 0 ? true
	: ring_buffer(result, size, nil)
;
@*/
{	
	struct ring_buffer *ring_buffer = malloc(sizeof (struct ring_buffer));
	if (ring_buffer == 0) return 0;
	int *fields = malloc(size * sizeof (int));
	if (fields == 0){
		free(ring_buffer);
		return 0;
	}
	//@ chars_to_int_array(fields, size);
	ring_buffer->fields =  fields;
	ring_buffer->size = size;
	ring_buffer->first = 0;
	ring_buffer->len = 0;
	//@ close ring_buffer(ring_buffer, size, nil);
	return ring_buffer;
}

void ring_buffer_dispose(struct ring_buffer *ring_buffer)
    //@ requires ring_buffer(ring_buffer, ?size, ?items);
    //@ ensures true;
{
    //@ open ring_buffer(ring_buffer, size, items);
    int* fields = ring_buffer->fields;
    //@ int_array_to_chars(fields);
    free(fields);
    free(ring_buffer);
}

void ring_buffer_clear(struct ring_buffer *ring_buffer)
    //@ requires ring_buffer(ring_buffer, ?size, ?items);
    //@ ensures ring_buffer(ring_buffer, size, nil);
{
    //@ open ring_buffer(ring_buffer, size, items);
    ring_buffer->len = 0;
    //@ close ring_buffer(ring_buffer, size, nil);
}

int ring_buffer_head(struct ring_buffer *ring_buffer)
    //@ requires ring_buffer(ring_buffer, ?size, ?items) &*& length(items) > 0;
    //@ ensures ring_buffer(ring_buffer, size, items) &*& result == head(items);
{
    //@ open ring_buffer(ring_buffer, size, items);
    int* fields = ring_buffer->fields;
    int offset = ring_buffer->first;
    //@ assert array<int>(fields, size, sizeof(int), integer, ?elems);
    //@ array_split(fields, offset);
    //@ open array(fields+offset, size-offset, _, _, _);
    int result = *(fields+offset);
    //@ array_unseparate_same(fields, elems);
    //@ close ring_buffer(ring_buffer, size, items);
    return result; 
}

void ring_buffer_push(struct ring_buffer *ring_buffer, int element)
//@ requires ring_buffer(ring_buffer, ?size, ?items) &*& length(items) < size;
//@ ensures ring_buffer(ring_buffer, size, append(items, cons(element, nil))); 
{
    //@ open ring_buffer(ring_buffer, size, items);
    //@ assert ring_buffer->first |-> ?first;
    int size2 = ring_buffer->size;
    int offset = ring_buffer->first + ring_buffer->len;
    if(offset >= size2) offset -= size2; //instead of modulo
    int* fields = ring_buffer->fields;
    //@ assert array<int>(fields, size, sizeof(int), integer, ?elems);
    //@ array_split(fields, offset);
    //@ open array(fields+offset, size-offset, _, _, _);
    *(fields+offset) = element;
    //@ array_unseparate(fields, offset, elems);
    ring_buffer->len++;
    //@ assert array<int>(fields, size, sizeof(int), integer, update(offset, element, elems));
    //@ assert items == take(length(items),append(drop(first, elems), take(first, elems)));
    
    //@ assert (append(items, cons(element, nil)) == take(length(items)+1,append(drop(first, update(offset, element, elems)), take(first, update(offset, element, elems)))));
    //@ close ring_buffer(ring_buffer, size, append(items, cons(element, nil)));
}

int ring_buffer_pop(struct ring_buffer *ring_buffer)
//@ requires ring_buffer(ring_buffer, ?size, ?items) &*& length(items) > 0;
//@ ensures ring_buffer(ring_buffer, size, tail(items)) &*& result == head(items); 
{
    int result = ring_buffer_head(ring_buffer);
    //@ open ring_buffer(ring_buffer, size, items);
    int size2 = ring_buffer->size;
    int newfirst = ring_buffer->first + 1;
    if(newfirst >= size2) newfirst -= size2; //instead of modulo
    ring_buffer->first = newfirst;
    ring_buffer->len--;
    //@ switch(items) { case nil: case cons(ih, it): } //switch to force case analysis
    //@ assert array<int>(?fields, size, sizeof(int), integer, ?elems);
    //@ assert (tail(items) == take(length(items)-1,append(drop(newfirst, elems), take(newfirst, elems))));
    //@ close ring_buffer(ring_buffer, size, tail(items));
    return result;   
}