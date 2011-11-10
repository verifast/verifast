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

bool is_split_up(int size, int first, int len)
//@ requires size * 4 < INT_MAX &*& len <= size;
//@ ensures result == is_split_up_fp(size, first, len);
{
	return first + len > size;
}
/*@
fixpoint bool size_is_ok(int size){
	return size * 4 < INT_MAX;
}

fixpoint bool is_split_up_fp(int size, int first, int len){
	return first + len > size;
}

fixpoint bool is_inside(int size, int first, int len, int needle){
	return is_split_up_fp(size, first, len) ?
		// it's split up: BIGTAILemptyBIGHEAD
		// Check if it's not in "empty"
		! ( (needle < first && needle >= (first + len) - size)	)
	:
		// it's not split up: emptySTUFFempty.
		// Check if it's in stuff:
		needle >= first && needle < first + len;	
}

fixpoint int bighead_size(int size, int first, int len){
	return size - first;
}


fixpoint int bigtail_size(int size, int first, int len){
	return len - bighead_size(size, first, len);
}



// Convert the "nth element in the array" to the "nth element in the queue"
fixpoint int array_id_to_queue_id(int size, int first, int len, int array_id){
	return
		! is_inside(size, first, len, array_id) ?
			-1 // Caller is wrong. Put garbage to find it more easily.
		:
			is_split_up_fp(size, first, len) ?
				array_id >= first ? // It's in capitalcased STUFF-part of stuff_emptySTUFF (=bighead)
					array_id - first
				: // It's in capitalcased part of STUFF_empty_stuff (=bigtail)
					array_id + (size - first)
			:
				array_id - first
	;
}

// I dislike catching by-one errors. Testing is faster.
lemma void is_inside_test()
	requires true;
	ensures true;
{
	assert is_inside(10, 3, 3, 3) == true;
	assert is_inside(10, 3, 3, 5) == true;
	assert is_inside(10, 3, 3, 6) == false;
	assert is_inside(10, 3, 3, 2) == false;
	
	assert is_inside(7, 5, 3, 4) == false;
	assert is_inside(7, 5, 3, 1) == false;
	assert is_inside(7, 5, 3, 0) == true;
	assert is_inside(7, 5, 3, 6) == true;
	
	assert is_inside(7, 5, 0, 6) == false;
	assert is_inside(7, 5, 0, 4) == false;
	assert is_inside(7, 5, 0, 0) == false;
}
lemma void array_id_to_queue_id_test()
	requires true;
	ensures true;
{
	assert array_id_to_queue_id(6,0,3,0) == 0;
	assert array_id_to_queue_id(6,1,3,1) == 0;
	assert array_id_to_queue_id(6,3,5,3) == 0;
	assert array_id_to_queue_id(6,3,5,4) == 1;
	assert array_id_to_queue_id(6,3,5,1) == 4;
}

// Ow this exists already. Nice.
//lemma void append_assoc<t>(list<t>l1, list<t> l2, list<t> l3);
//requires true;
//ensures append(l1, append(l2, l3)) == append(append(l1, l2), l3);

predicate ring_buffer(struct ring_buffer *buffer, int size, int first, int len, list<int> items) =
	
	size >= 0 && size * 4 < INT_MAX
	&*& len <= size
	&*& first >= 0 && first < size
	
	&*& length(items) == len
	
	&*& buffer->fields |-> ?fields
	&*& buffer->size |-> size
	&*& buffer->first |-> first
	&*& buffer->len |-> len
	
	&*& malloc_block(fields, 4 * size)
	&*& malloc_block_ring_buffer(buffer)
	
	
	&*& is_split_up_fp(size, first, len) ?
	
		// Bigtail
		array<int>(fields, bigtail_size(size, first, len), sizeof(int), integer, ?bigtail_elems)
	
		// emptyness
		&*& array<int>(fields + bigtail_size(size, first, len), size - len, sizeof(int), integer, _)
		
		// Bighead
		&*& array<int>(fields + first, bighead_size(size, first, len), sizeof(int), integer, ?bighead_elems)
		
		// make sure verification knows all arrays are next to each other.
		&*& first == bigtail_size(size, first, len) + (size - len)
		
		&*& append(bighead_elems, bigtail_elems) == items
		
	:
		// leading emptyness
		array<int>(fields, first, sizeof(int), integer, _)
		
		// Elems
		&*& array<int>(fields + first, len, sizeof(int), integer, items)
		
		// trailing emptyness
		&*& array<int>(fields + first + len, size - len - first, sizeof(int), integer, _)
	;
	
@*/

/*@
// XXX Why is this missing in arrays.h??? (probably because of generics<t> and sizeof(t)?)
lemma void chars_to_pointer_array(void *ptr);
    requires
        [?f]chars(ptr, ?orig_elems);
    ensures
        [f]array<void*>(ptr, length(orig_elems), sizeof(void*), pointer, ?orig_array_elems)
        &*& length(orig_array_elems) * sizeof(void*) == length(orig_elems)
        &*& length(orig_array_elems) == length(orig_elems);
@*/

struct ring_buffer *ring_buffer_create(int size)
//@ requires size >= 1 &*& size * sizeof(int) < INT_MAX;
/*@ ensures
	result == 0 ? true
	: ring_buffer(result, size, 0, 0, nil)
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
	//@ close ring_buffer(ring_buffer, size, 0, 0, nil);
	return ring_buffer;
}

// i.e. add to end of queue.
void ring_buffer_push(struct ring_buffer *ring_buffer, int element)
/*@ requires ring_buffer(ring_buffer, ?size, ?first, ?len, ?items)
	// XXX extra stuff to make it more easy:
	&*& len < size - 2 &*& first + len < size - 1;
@*/
//@ ensures ring_buffer(ring_buffer, size, first, len+1, ?items2) &*& append(items, cons(element, nil)) == items2; //take(len, items2) == items;
{

	//@ open ring_buffer(ring_buffer, size, first, len, items);
	//@ assert ring_buffer->fields |-> ?fields;
	int put_at;
	if (is_split_up(ring_buffer->size, ring_buffer->first, ring_buffer->len+1)){
		//@ assert is_split_up_fp(size, first, len) == true;
		put_at = ring_buffer->len - (ring_buffer->size - ring_buffer->first);
		
		//@ assert array<int>(fields, bigtail_size(size, first, len), sizeof(int), integer, ?bigtail_elems);
		//@ assert array<int>(fields + first, _, _, _, ?bighead_elems);
		//@ open array<int>(ring_buffer->fields + bigtail_size(size, first, len), size - len, sizeof(int), integer, _); // open <s>happyness</s>emptyness.
		*(ring_buffer->fields+put_at) = element;
		// append to bigtail:
		//@ close array<int>(ring_buffer->fields+put_at, 1, sizeof(int), integer, cons(element, nil)); // array of size one
		
		//@ append_assoc(bighead_elems, bigtail_elems, cons(element, nil));
		
		//@ array_merge<int>(ring_buffer->fields);
		
		
	}else{
		//@ assert ! is_split_up_fp(size, first, len) == true;
		put_at = ring_buffer->first + ring_buffer->len;
		//@ open array<int>(fields + first + len, _, _, _, _); // open trailing emptyness
		*(ring_buffer->fields+put_at) = element;
		//@ close array<int>(ring_buffer->fields+put_at, 1, sizeof(int), integer, cons(element, nil)); // array of size one
		//@ array_merge<int>(ring_buffer->fields+first);
	}
	ring_buffer->len++;
	//@ close ring_buffer(ring_buffer, size, first, len+1, append(items, cons(element, nil)));
}


// i.e. remove from beginning of queue
//void *ring_buffer_pop(struct ring_buffer *ring_buffer)
