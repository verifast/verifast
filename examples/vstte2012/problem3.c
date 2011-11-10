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
//@ requires size * 4 < INT_MAX &*& len <= size &*& len >= 0;
//@ ensures result == is_split_up_fp(size, first, len);
{
	return first > size - len;
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
	
	&*& malloc_block(fields, sizeof(int) * size)
	&*& malloc_block_ring_buffer(buffer)

	&*& fields + size <= (void*)UINTPTR_MAX
	
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
	//@ chars_limits((void*)fields);
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
/*@ requires
	ring_buffer(ring_buffer, ?size, ?first, ?len, ?items)
	&*& len < size // you can't push more elements if it's already full.
	;
@*/
//@ ensures ring_buffer(ring_buffer, size, first, len+1, ?items2) &*& append(items, cons(element, nil)) == items2;
{

	//@ open ring_buffer(ring_buffer, size, first, len, items);
	//@ assert ring_buffer->fields |-> ?fields;
	
	int put_at;
	if (is_split_up(ring_buffer->size, ring_buffer->first, ring_buffer->len+1)){
		put_at = ring_buffer->len - (ring_buffer->size - ring_buffer->first);
		
		//@ assert array<int>(fields, bigtail_size(size, first, len), sizeof(int), integer, ?bigtail_elems);
		//@ assert array<int>(fields + first, bighead_size(size, first, len), _, _, ?bighead_elems);

		//@ open array<int>(ring_buffer->fields + bigtail_size(size, first, len), size - len, sizeof(int), integer, _); // open <s>happyness</s>emptyness.
		*(ring_buffer->fields+put_at) = element;

		//@ close array<int>(ring_buffer->fields+put_at, 1, sizeof(int), integer, cons(element, nil)); // array of size one
		//@ append_assoc(bighead_elems, bigtail_elems, cons(element, nil));
		
		/*@
		// Only need to merge if there is something to merge width, i.e. this is not the first element of bigtail.
		if (is_split_up_fp(size,first,len)){
			array_merge<int>(ring_buffer->fields);
		}
		@*/
		
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


/*@
lemma void test_appendtail<t>(list<t> l1, list<t> l2, t item, list<t> l3)
requires l1 == cons(item, nil) &*& append(l1, l2) == l3;
ensures tail(l3) == l2;
{
}
@*/

/*@
lemma void tail_of_singleton_is_nil<t>(list<t> l);
requires length(l) == 1;
ensures tail(l) == nil;
// Meh. Prove doesn't work yet. XXX
@*/


// i.e. remove from beginning of queue
int ring_buffer_pop(struct ring_buffer *ring_buffer)
/*@ requires
	ring_buffer(ring_buffer, ?size, ?first, ?len, ?elems)
	&*& len > 0 // you can't pop nonexisting elements
	;
@*/
//@ ensures ring_buffer(ring_buffer, size, first == size - 1 ? 0 : first + 1, len-1, tail(elems)) &*& result == head(elems);
{
	//@ open ring_buffer(ring_buffer, _, _, _, _);
	int take_at = ring_buffer->first;
	int elem;
	//@ int  newfirst = first + 1 == size ? 0 : first + 1;
	//@ assert ring_buffer->fields |-> ?fields;
	
	//@ open array(ring_buffer->fields + first, _, _, _, ?elems_bighead);
	elem = *(ring_buffer->fields + take_at);
	ring_buffer->len = ring_buffer->len - 1;
	ring_buffer->first = ring_buffer->first + 1;
	if (ring_buffer->first == ring_buffer->size) ring_buffer->first = 0; // XXX hmm why can we also assign "first = ..." here if first is ghost??

	
	/*@
	if (bighead_size(size, first, len) == 1){
		assert newfirst == 0;
		tail_of_singleton_is_nil(elems_bighead);
		
		close array<int>(fields + take_at, 1, sizeof(int), integer, cons(elem, nil)); // array size one
		array_merge(fields + len-1);
	}else{
		close array<int>(ring_buffer->fields + take_at + 1, 0, sizeof(int), integer, nil);

		close array<int>(fields + take_at, 1, sizeof(int), integer, cons(elem, nil)); // array size one
		if (is_split_up_fp(size, first, len)){
			array_merge(ring_buffer->fields + bigtail_size(size, first, len));
			if ( ! is_split_up_fp(size, newfirst, len-1)){
				// convert to non-split up data structure
			
				// zero-size leading emptyness
				close array<int>(fields, 0, sizeof(int), integer, nil);
				assert bighead_size(size, first, len) == 1;
				//assert false;
			}
		}else{
			// Make trailing emptyness a bit larger
			assert array<int>(fields + first + len, size - first - len, sizeof(int), integer, ?trailing_emptyness_data);
		
			array_merge(ring_buffer->fields);
		}
	}
	@*/
	//@close ring_buffer(ring_buffer, size, newfirst, len-1,  tail(elems));
	
	return elem;
		
}
