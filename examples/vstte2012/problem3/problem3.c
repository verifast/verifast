#include "malloc.h"
//@ #include "arrays.gh"
//@ #include "listex.gh"
#include "problem3.h"

/*
Terminology: if the array is STUFF1_empty_STUFF2, then bighead refers to stuff2, bigtail refers to stuff1.
*/

struct ring_buffer{
	int *fields; // buffer contents
	int size;
	int first; // start counting with 0
	int len;
};

bool is_split_up(int size, int first, int len)
//@ requires size * sizeof(int) < INT_MAX &*& len <= size &*& len >= 0;
//@ ensures result == is_split_up_fp(size, first, len);
{
	return first > size - len;
}
/*@
fixpoint bool is_split_up_fp(int size, int first, int len){
	return first > size - len;
}

fixpoint int bighead_size(int size, int first, int len){
	return size - first;
}


fixpoint int bigtail_size(int size, int first, int len){
	return len - bighead_size(size, first, len);
}


predicate ring_buffer(struct ring_buffer *buffer; int size, list<int> items) =
	buffer->fields |-> ?fields
	&*& buffer->size |-> size
	&*& buffer->first |-> ?first
	&*& buffer->len |-> ?len
	
	&*& size >= 0 && size * sizeof(int) < INT_MAX
	&*& len <= size
	&*& first >= 0 && first < size
	&*& length(items) == len
	
	&*& malloc_block_ints(fields, size)
	&*& malloc_block_ring_buffer(buffer)

	&*& pointer_within_limits(fields + size) == true
	
	&*& is_split_up_fp(size, first, len) ?
	
		// Bigtail
		fields[0..bigtail_size(size, first, len)] |-> ?bigtail_elems
	
		// emptyness
		&*& ints_(fields + bigtail_size(size, first, len), size - len, _)
		
		// Bighead
		&*& ints(fields + first, bighead_size(size, first, len), ?bighead_elems)
		
		// make sure verification knows all arrays are next to each other.
		&*& first == bigtail_size(size, first, len) + (size - len)
		
		&*& items == append(bighead_elems, bigtail_elems)
		
	:
		// leading emptyness
		ints_(fields, first, _)
		
		// Elems
		&*& ints(fields + first, len, items)
		
		// trailing emptyness
		&*& ints_(fields + first + len, size - len - first, _)
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
	ring_buffer->fields =  fields;
	ring_buffer->size = size;
	ring_buffer->first = 0;
	ring_buffer->len = 0;
	
	//@ close ring_buffer(ring_buffer, size, nil);
	return ring_buffer;
}

// i.e. add to end of queue.
void ring_buffer_push(struct ring_buffer *ring_buffer, int element)
/*@ requires
	ring_buffer(ring_buffer, ?size, ?items)
	&*& length(items) < size // you can't push more elements if it's already full.
	;
@*/
//@ ensures ring_buffer(ring_buffer, size, ?items2) &*& append(items, cons(element, nil)) == items2;
{

	//@ open ring_buffer(ring_buffer, size, items);
	//@ assert ring_buffer->fields |-> ?fields;
	//@ assert ring_buffer->first |-> ?first;
	//@ assert ring_buffer->len |-> ?len;
	
	int put_at;
	if (is_split_up(ring_buffer->size, ring_buffer->first, ring_buffer->len+1)){
		put_at = ring_buffer->len - (ring_buffer->size - ring_buffer->first);
		
		//@ assert ints(fields, bigtail_size(size, first, len), ?bigtail_elems);
		//@ assert ints(fields + first, bighead_size(size, first, len), ?bighead_elems);

		//@ open ints_(ring_buffer->fields + bigtail_size(size, first, len), size - len, _); // open <s>happyness</s>emptyness.
		*(ring_buffer->fields+put_at) = element;

		//@ close ints(ring_buffer->fields+put_at, 1, cons(element, nil)); // array of size one
		//@ append_assoc(bighead_elems, bigtail_elems, cons(element, nil));
		
		/*@
		// Only need to merge if there is something to merge width, i.e. this is not the first element of bigtail.
		if (is_split_up_fp(size,first,len)){
			ints_join(ring_buffer->fields);
		}
		@*/
		
	}else{
		//@ assert ! is_split_up_fp(size, first, len) == true;
		put_at = ring_buffer->first + ring_buffer->len;
		//@ open ints_(fields + first + len, _, _); // open trailing emptyness
		*(ring_buffer->fields+put_at) = element;
		//@ close ints(ring_buffer->fields+put_at, 1, cons(element, nil)); // array of size one
		//@ ints_join(ring_buffer->fields+first);
	}
	ring_buffer->len++;
	//@ close ring_buffer(ring_buffer, size, append(items, cons(element, nil)));
}

/*@
lemma void tail_of_singleton_is_nil<t>(list<t> l)
  requires length(l) == 1;
  ensures tail(l) == nil;
{
  switch (l) {
    case nil:
    case cons(lh, lt):
      switch (lt) {
        case nil:
        case cons(lth, ltt):
      }
  }
}
@*/

void ring_buffer_clear(struct ring_buffer *ring_buffer)
//@ requires ring_buffer(ring_buffer, ?size, ?elems);
//@ ensures ring_buffer(ring_buffer, size, nil);
{
	//@ open ring_buffer(ring_buffer, size, elems);
	/*@
	if (ring_buffer->first > ring_buffer->size - ring_buffer->len) {
	  ints_to_ints_(ring_buffer->fields);
	  ints__join(ring_buffer->fields);
	  ints_to_ints_(ring_buffer->fields + ring_buffer->first);
	  ints__join(ring_buffer->fields);
	} else {
	  ints_to_ints_(ring_buffer->fields + ring_buffer->first);
	  ints__join(ring_buffer->fields);
	  ints__join(ring_buffer->fields);
        }
        @*/
	ring_buffer->len = 0;
	//@ ints__split(ring_buffer->fields,ring_buffer->first);
	//@ close ring_buffer(ring_buffer, size, nil);
}


int ring_buffer_head(struct ring_buffer *ring_buffer)
//@ requires ring_buffer(ring_buffer, ?size, ?elems) &*& length(elems) > 0;
//@ ensures ring_buffer(ring_buffer, size, elems) &*& result == head(elems);
{
	//@ open ring_buffer(ring_buffer, size, elems);
	//@ open ints(ring_buffer->fields + ring_buffer->first, _, _);
	return *(ring_buffer->fields + ring_buffer->first);
	//@ close ring_buffer(ring_buffer, size, elems);
	
}

// i.e. remove from beginning of queue
int ring_buffer_pop(struct ring_buffer *ring_buffer)
/*@ requires
	ring_buffer(ring_buffer, ?size, ?elems)
	&*& length(elems) > 0 // you can't pop nonexisting elements
	;
@*/
//@ ensures ring_buffer(ring_buffer, size, tail(elems)) &*& result == head(elems);
{
	//@ open ring_buffer(ring_buffer, _, _);
	//@ assert ring_buffer->first |-> ?first;
	//@ assert ring_buffer->len |-> ?len;
	int take_at = ring_buffer->first;
	int elem;
	//@ int  newfirst = first + 1 == size ? 0 : first + 1;
	//@ assert ring_buffer->fields |-> ?fields;
	
	//@ open ints(ring_buffer->fields + first, _, ?elems_bighead);
	elem = *(ring_buffer->fields + take_at);
	ring_buffer->len = ring_buffer->len - 1;
	ring_buffer->first = ring_buffer->first + 1;
	if (ring_buffer->first == ring_buffer->size) ring_buffer->first = 0; // XXX hmm why can we also assign "first = ..." here if first is ghost??

	
	/*@
	if (bighead_size(size, first, len) == 1){
		assert newfirst == 0;
		switch (elems_bighead) { case nil: case cons(h, t): switch (t) { case nil: case cons(th, tt): } }
		
		close ints_(fields + take_at, 1, cons(some(elem), _)); // array size one
		ints__join(fields + len-1);
	}else{
		close ints(ring_buffer->fields + take_at + 1, 0, nil);

		close ints_(fields + take_at, 1, cons(some(elem), nil)); // array size one
		if (is_split_up_fp(size, first, len)){
			ints__join(ring_buffer->fields + bigtail_size(size, first, len));
		}else{
			// Make trailing emptyness a bit larger
			assert ints_(fields + first + len, size - first - len, ?trailing_emptyness_data);
		
			ints__join(ring_buffer->fields);
		}
	}
	@*/
	//@close ring_buffer(ring_buffer, size, tail(elems));
	
	return elem;
		
}

void ring_buffer_dispose(struct ring_buffer *ring_buffer)
//@ requires ring_buffer(ring_buffer, _, _);
//@ ensures true;
{
	//@ open ring_buffer(ring_buffer, _, _);
	/*@
	if (ring_buffer->first > ring_buffer->size - ring_buffer->len) {
	  ints_to_ints_(ring_buffer->fields);
	  ints__join(ring_buffer->fields);
	  ints_to_ints_(ring_buffer->fields + ring_buffer->first);
	  ints__join(ring_buffer->fields);
	} else {
	  ints_to_ints_(ring_buffer->fields + ring_buffer->first);
	  ints__join(ring_buffer->fields);
	  ints__join(ring_buffer->fields);
        }
        @*/
	free(ring_buffer->fields);
	free(ring_buffer);
}

bool ring_buffer_is_full(struct ring_buffer *ring_buffer)
//@ requires ring_buffer(ring_buffer, ?size, ?items);
//@ ensures ring_buffer(ring_buffer, size, items) &*& result == (length(items) == size) &*& length(items) <= size;
{
	//@ open ring_buffer(_, _, _);
	return ring_buffer->len == ring_buffer->size;
	//@ close ring_buffer(ring_buffer, size, items);
}

bool ring_buffer_is_empty(struct ring_buffer *ring_buffer)
//@ requires ring_buffer(ring_buffer, ?size, ?items);
//@ ensures ring_buffer(ring_buffer, size, items) &*& result == (length(items) == 0) &*& length(items) >= 0;
{
	//@ open ring_buffer(_, _, _);
	return ring_buffer->len == 0;
	//@ close ring_buffer(ring_buffer, size, items);
}


void harness(int x, int y, int z)
//@ requires true;
//@ ensures true;
{
	struct ring_buffer *b = ring_buffer_create(2);
	if (b == 0) return;
	ring_buffer_push(b, x);
	ring_buffer_push(b, y);
	int h = ring_buffer_pop(b);
	//@ assert h == x;
	ring_buffer_push(b, z);
	h = ring_buffer_pop(b);
	//@ assert h == y;
	h = ring_buffer_pop(b);
	//@ assert h == z;
	ring_buffer_dispose(b);
	
}

int main() //@ : main
//@ requires true;
//@ ensures true;
{
  harness(1, 2, 3);
  return 0;
}