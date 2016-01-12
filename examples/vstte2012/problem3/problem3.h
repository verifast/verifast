#ifndef __PROBLEM3_H
#define __PROBLEM3_H

struct ring_buffer;
/*@
predicate ring_buffer(struct ring_buffer *buffer; int size, list<int> items);
@*/

struct ring_buffer *ring_buffer_create(int size);
//@ requires size >= 1 &*& size * sizeof(int) < INT_MAX;
/*@ ensures
	result == 0 ? true
	: ring_buffer(result, size, nil)
;
@*/


void ring_buffer_dispose(struct ring_buffer *ring_buffer);
    //@ requires ring_buffer(ring_buffer, ?size, ?items);
    //@ ensures true;


void ring_buffer_clear(struct ring_buffer *ring_buffer);
    //@ requires ring_buffer(ring_buffer, ?size, ?items);
    //@ ensures ring_buffer(ring_buffer, size, nil);

int ring_buffer_head(struct ring_buffer *ring_buffer);
    //@ requires ring_buffer(ring_buffer, ?size, ?items) &*& length(items) > 0;
    //@ ensures ring_buffer(ring_buffer, size, items) &*& result == head(items);

void ring_buffer_push(struct ring_buffer *ring_buffer, int element);
//@ requires ring_buffer(ring_buffer, ?size, ?items) &*& length(items) < size;
//@ ensures ring_buffer(ring_buffer, size, append(items, cons(element, nil))); 


int ring_buffer_pop(struct ring_buffer *ring_buffer);
//@ requires ring_buffer(ring_buffer, ?size, ?items) &*& length(items) > 0;
//@ ensures ring_buffer(ring_buffer, size, tail(items)) &*& result == head(items); 

bool ring_buffer_is_full(struct ring_buffer *ring_buffer);
//@ requires ring_buffer(ring_buffer, ?size, ?items);
//@ ensures ring_buffer(ring_buffer, size, items) &*& result == (length(items) == size) &*& length(items) <= size;

bool ring_buffer_is_empty(struct ring_buffer *ring_buffer);
//@ requires ring_buffer(ring_buffer, ?size, ?items);
//@ ensures ring_buffer(ring_buffer, size, items) &*& result == (length(items) == 0) &*& length(items) >= 0;

#endif