#include "malloc.h"
#include "problem3.h"
//@ #include "arrays.gh"
//@ #include "listex.gh"

struct ring_buffer{
	int *fields; // buffer contents
	int size;
	int first; // start counting with 0
	int len;
};

/*@

predicate ring_buffer(struct ring_buffer *buffer; int size, list<int> items) =
	size >= 0 && size * 4 < INT_MAX
	
	&*& buffer->fields |-> ?fields
	&*& buffer->size |-> size
	&*& buffer->first |-> ?first
	&*& buffer->len |-> ?len
	&*& first >= 0 && first < size
	&*& length(items) == len
	&*& len <= size  
	&*& pointer_within_limits(fields + size) == true
	
	&*& malloc_block_ints(fields, size)
	&*& malloc_block_ring_buffer(buffer)
	&*& fields[0..size] |-> ?elems
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
	int *fields = calloc(size, sizeof(int));
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

void ring_buffer_dispose(struct ring_buffer *ring_buffer)
    //@ requires ring_buffer(ring_buffer, ?size, ?items);
    //@ ensures true;
{
    //@ open ring_buffer(ring_buffer, size, items);
    int* fields = ring_buffer->fields;
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
    //@ assert ints(fields, size, ?elems);
    //@ ints_split(fields, offset);
    //@ open ints(fields+offset, size-offset, _);
    int result = *(fields+offset);
    //@ ints_unseparate_same(fields, elems);
    //@ close ring_buffer(ring_buffer, size, items);
    return result; 
}
/*@
lemma void append_take_drop<t>(int n, list<t> l)
    requires 0 <= n;
    ensures append(take(n, l), drop(n, l)) == l;
{
    switch(l) {
        case nil:
        case cons(h, t):
            if(n != 0) {
                append_take_drop(n-1, t);
            }
    } 
}

lemma void update_append<t>(int n, t elem, list<t> l1, list<t> l2) 
    requires 0 <= n;
    ensures update(n, elem, append(l1, l2)) == (n < length(l1) ? append(update(n, elem, l1), l2) : append(l1, update(n-length(l1), elem, l2)));
{
    switch(l1) {
        case nil:
        case cons(h, t):
            if(n != 0) {
                update_append(n-1, elem, t, l2);
            }
    } 
}

lemma void update_drop_take<t>(int n, t elem, list<t> elems) 
    requires 0 <= n &*& n < length(elems);
    ensures update(n, elem, elems) == append(take(n, elems), cons(elem, drop(n+1, elems)));
{
    switch(elems) {
        case nil:
        case cons(h, t):
            if(n != 0) {
                update_drop_take(n-1, elem, t);
            }
    } 
}

lemma void take_append_alt<t>(int n, list<t> l1, list<t> l2)
    requires n >= 0; 
    ensures take(n, append(l1, l2)) == (n <= length(l1) ? take(n, l1) : append(l1, take(n-length(l1), l2)));
{
    switch(l1) {
        case nil:
        case cons(h, t): if(n!=0) take_append_alt(n-1, t, l2);
    }
}

lemma void drop_append_alt<t>(int n, list<t> l1, list<t> l2)
    requires n >= 0; 
    ensures drop(n, append(l1, l2)) == (n <= length(l1) ? append(drop(n, l1), l2) : drop(n-length(l1), l2));
{
    switch(l1) {
        case nil:
        case cons(h, t): if(n!=0) drop_append_alt(n-1, t, l2);
    }
}

lemma void append_split<t>(list<t> l1, list<t> l2)
    requires true; 
    ensures take(length(l1), append(l1, l2)) == l1 &*& drop(length(l1),append(l1, l2)) == l2;
{
    switch(l1) {
        case nil:
        case cons(h, t): append_split(t, l2);
    }
}
lemma void take_over_take<t>(int n1, int n2, list<t> l)
    requires 0<=n1 &*& n1 <= n2;
    ensures take(n1, take(n2, l)) == take(n1, l);
{
    switch(l) {
        case nil:
        case cons(h,t): if(n1>0) take_over_take(n1-1, n2-1, t);
    }
}

@*/

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
    //@ assert ints(fields, size, ?elems);
    //@ ints_split(fields, offset);
    //@ open ints(fields+offset, size-offset, _);
    *(fields+offset) = element;
    //@ ints_unseparate(fields, offset, elems);
    ring_buffer->len++;
    //@ assert ints(fields, size, update(offset, element, elems));
    //@ assert items == take(length(items),append(drop(first, elems), take(first, elems)));
    //@ append_take_drop(first, elems);
    //@ take_append_alt(length(items), drop(first, elems), take(first, elems));
    //@ update_append(offset, element, take(first, elems), drop(first, elems));
    /*@
        if(first <= offset) {
            append_take_drop(offset-first, drop(first, elems));
            assert elems == append(take(first, elems), append(take(offset-first, drop(first,elems)), drop(offset-first, drop(first,elems))));
            assert length(items) == offset-first;            
            assert items == take(offset-first, drop(first,elems));
            assert update(offset, element, elems) == append(take(first, elems), update(offset-first, element, drop(first, elems)));
            append_split(take(first, elems), update(offset-first, element, drop(first, elems)));
            assert take(first, update(offset, element, elems)) == take(first, elems); 
            assert drop(first, update(offset, element, elems)) == update(offset-first, element, drop(first, elems));
            //update_drop_take(offset-first, element, drop(first, elems));
            take_append_alt(length(items)+1, update(offset-first, element, drop(first, elems)), take(first, elems));
            assert take(length(items)+1, append(update(offset-first, element, drop(first, elems)), take(first, elems))) ==
                   take(length(items)+1, update(offset-first, element, drop(first, elems)));
            update_append(offset-first, element, take(offset-first, drop(first, elems)), drop(offset-first, drop(first, elems)));
            take_append_alt(length(items)+1, take(offset-first, drop(first,elems)), update(0, element, drop(offset-first, drop(first,elems))));
            switch(drop(offset-first, drop(first, elems))) { case nil: case cons(h, t): }
            assert take(length(items)+1, update(offset-first, element, drop(first, elems))) == 
                   append(take(offset-first, drop(first,elems)), cons(element, nil));
            assert (append(items, cons(element, nil)) == take(length(items)+1,append(update(offset-first, element, drop(first, elems)), take(first, elems))));
        } else {
            append_take_drop(offset, take(first, elems));
            assert take(first, elems) == append(take(offset, take(first,elems)), drop(offset, take(first,elems)));
            assert elems == append(take(first, elems), drop(first, elems));
            //assert elems == append(append(take(offset, take(first,elems)), drop(offset, take(first,elems))), drop(first, elems));
            assert length(items) == length(drop(first, elems)) + length(take(offset, take(first,elems)));
            assert items == take(length(items), append(drop(first, elems), take(first, elems)));
            assert items == append(drop(first, elems), take(offset, take(first,elems)));
            
            assert update(offset, element, elems) == append(update(offset, element, take(first, elems)), drop(first, elems));
            append_split(update(offset, element, take(first, elems)), drop(first, elems));
            assert take(first, update(offset, element, elems)) == update(offset, element, take(first, elems)); 
            assert drop(first, update(offset, element, elems)) == drop(first, elems);
            update_append(offset, element, take(offset, take(first, elems)), drop(offset, take(first, elems)));
            assert take(length(items)+1, append(drop(first, elems), update(offset, element, take(first, elems)))) ==
                   take(length(items)+1, append(drop(first, elems), append(take(offset, take(first, elems)), update(0, element, drop(offset, take(first, elems))))));
            take_append_alt(length(items)+1, drop(first, elems), update(offset, element, take(first, elems)));
            take_append_alt(length(items)+1-length(drop(first, elems)), take(offset, take(first, elems)), update(0, element, drop(offset, take(first, elems))));
            assert take(length(items)+1, append(drop(first, elems), update(offset, element, take(first, elems)))) ==
                   append(drop(first, elems), append(take(offset, take(first, elems)), take(1, update(0, element, drop(offset, take(first, elems))))));
                   
            switch(drop(offset, take(first, elems))) { case nil: case cons(h,t): }
            assert update(0, element, drop(offset, take(first, elems))) == cons(element, tail(drop(offset, take(first, elems))));
            assert take(1, update(0, element, drop(offset, take(first, elems)))) == cons(element, nil);
            
            assert take(length(items)+1, append(drop(first, elems), update(offset, element, take(first, elems)))) ==
                   append(drop(first, elems), append(take(offset, take(first, elems)), cons(element, nil)));
            append_assoc(drop(first, elems), take(offset, take(first, elems)), cons(element, nil));
            assert (append(items, cons(element, nil)) == take(length(items)+1,append(drop(first, elems), update(offset, element, take(first, elems)))));
        }
    @*/
    
    //@ assert (append(items, cons(element, nil)) == take(length(items)+1,append(drop(first, update(offset, element, elems)), take(first, update(offset, element, elems)))));
    //@ close ring_buffer(ring_buffer, size, append(items, cons(element, nil)));
}

int ring_buffer_pop(struct ring_buffer *ring_buffer)
//@ requires ring_buffer(ring_buffer, ?size, ?items) &*& length(items) > 0;
//@ ensures ring_buffer(ring_buffer, size, tail(items)) &*& result == head(items); 
{
    int result = ring_buffer_head(ring_buffer);
    //@ open ring_buffer(ring_buffer, size, items);
    //@ assert ring_buffer->first |-> ?first;
    int size2 = ring_buffer->size;
    int newfirst = ring_buffer->first + 1;
    if(newfirst >= size2) newfirst -= size2; //instead of modulo
    ring_buffer->first = newfirst;
    ring_buffer->len--;
    //@ switch(items) { case nil: case cons(ih, it): } //switch to force case analysis
    //@ assert ints(?fields, size, ?elems);
    //@ assert items == take(length(items),append(drop(first, elems), take(first, elems)));
    //@ append_take_drop(first, elems);
    /*@
        if(newfirst != 0) {
                assert items == take(length(items),append(drop(first, elems), take(first, elems)));
                assert newfirst == first + 1;
                switch(drop(first,elems)) { case nil: case cons(h,t): }
                drop_n_plus_one(first, elems);
                take_plus_one(first, elems);
                take_append_alt(length(items), drop(first, elems), take(first, elems));
                assert items == cons(nth(first, elems), take(length(items)-1,append(drop(first+1, elems), take(first, elems))));
                assert drop(newfirst, elems) == tail(drop(first, elems));
                assert take(newfirst, elems) == append(take(first, elems), cons(head(drop(first, elems)), nil)); 
                assert take(length(items)-1,append(drop(newfirst, elems), take(newfirst, elems))) == 
                       take(length(items)-1, append(tail(drop(first, elems)), append(take(first, elems), cons(head(drop(first, elems)), nil))));
                take_append_alt(length(items)-1, tail(drop(first, elems)), append(take(first, elems), cons(head(drop(first, elems)), nil)));
                assert length(drop(first, elems)) == length(elems) - first;
                if(length(items) < length(drop(first, elems))) {
                    assert (tail(items) == take(length(items)-1,append(drop(newfirst, elems), take(newfirst, elems))));
                } else {
                    take_append_alt(length(items)-length(drop(first, elems)), take(first, elems), cons(head(drop(first, elems)), nil));
                    assert (tail(items) == take(length(items)-1,append(drop(newfirst, elems), take(newfirst, elems))));
                }
        } else {
                assert elems == append(take(first, elems), drop(first, elems));
                assert first == size - 1;
                assert length(drop(first, elems)) == 1;                
                switch(drop(first,elems)) { case nil: case cons(h,t): switch(t) {case nil: case cons(h2,t2): }}
                assert head(items) == head(drop(first, elems));
                take_append_alt(length(items),drop(first, elems), take(first, elems));
                assert items == append(drop(first, elems), take(length(items)-1, take(first,elems)));
                assert tail(items) == take(length(items)-1, take(first, elems));
                take_append_alt(length(items)-1,drop(newfirst, elems), take(newfirst, elems));
                assert drop(0, elems) == elems &*& take(0, elems) == nil;
                append_nil(drop(newfirst, elems));
                assert take(length(items)-1, append(drop(newfirst, elems), take(newfirst, elems))) ==
                       take(length(items)-1, elems);
                assert length(items)-1 <= first;       
                take_over_take(length(items)-1, first, elems);
                assert (tail(items) == take(length(items)-1, append(drop(newfirst, elems), take(newfirst, elems))));
        }
    @*/
    //@ assert (tail(items) == take(length(items)-1,append(drop(newfirst, elems), take(newfirst, elems))));
    //@ close ring_buffer(ring_buffer, size, tail(items));
    return result;   
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


void test (int x, int y, int z) 
    //@ requires true;
    //@ ensures true;
{
    struct ring_buffer* b = ring_buffer_create(2);
    if(b==0) return;
    ring_buffer_push(b, x);
    ring_buffer_push(b, y);
    int h = ring_buffer_pop(b); 
    assert h == x;
    ring_buffer_push(b, z);
    h = ring_buffer_pop(b); 
    assert h == y;
    h = ring_buffer_pop(b); 
    assert h == z;
    ring_buffer_dispose(b);
}


int main() //@ : main
//@ requires true;
//@ ensures true;
{
  test(1, 2, 3);
  return 0;
}