#include <stdlib.h>
#include <stdint.h>
//@ #include <listex.gh>

struct Node {
    struct Node *prev;
    int32_t value;
    struct Node *next;
};

/*@

predicate nodes(struct Node *before, struct Node *first, struct Node *last, struct Node *after; list<int> elements) =
    first == after ?
        last == before &*& elements == nil
    :
        first->prev |-> before &*&
        first->value |-> ?value &*&
        first->next |-> ?next &*&
        malloc_block_Node(first) &*&
        nodes(first, next, last, after, ?elements0) &*&
        elements == cons(value, elements0);

predicate deque(struct Node *sentinel; list<int> elements) =
    sentinel->prev |-> ?last &*&
    sentinel->value |-> _ &*&
    sentinel->next |-> ?first &*&
    malloc_block_Node(sentinel) &*&
    nodes(sentinel, first, last, sentinel, elements);

@*/

struct Node *create_deque()
//@ requires true;
//@ ensures deque(result, nil);
{
    struct Node *sentinel = malloc(sizeof(struct Node));
    if (sentinel == 0) abort();
    (*sentinel).prev = sentinel;
    (*sentinel).next = sentinel;
    return sentinel;
}

void push_front(struct Node *deque, int32_t value)
//@ requires deque(deque, ?values);
//@ ensures deque(deque, cons(value, values));
{
    struct Node *n = malloc(sizeof(struct Node));
    if (n == 0) abort();
    (*n).prev = deque;
    (*n).value = value;
    (*n).next = (*deque).next;
    (*(*n).prev).next = n;
    //@ open nodes(deque, ?first, ?last, deque, values);
    (*(*n).next).prev = n;
}

/*@

lemma void deque_snoc()
    requires nodes(?before, ?first, ?last, ?after, ?values) &*& first != after;
    ensures
        nodes(before, first, ?last0, last, ?values0) &*&
        last->prev |-> last0 &*& last->value |-> ?value &*& last->next |-> after &*&
        malloc_block_Node(last) &*& values == append(values0, {value});
{
    open nodes(before, first, last, after, values);
    assert nodes(first, ?next, last, after, ?values1);
    if (next == after) {
        open nodes(first, next, last, after, values1);
        close nodes(before, first, before, last, nil);
    } else {
        deque_snoc();
        assert nodes(first, next, ?last0, last, ?values0);
        close nodes(before, first, last0, last, cons(head(values), values0));
    }
}

lemma void deque_add()
    requires
        nodes(?before, ?first, ?last, ?after, ?values) &*&
        after->prev |-> last &*&
        after->value |-> ?value &*&
        after->next |-> ?next &*& next->value |-> ?nextValue &*&
        malloc_block_Node(after);
    ensures
        nodes(before, first, after, next, append(values, {value})) &*& next->value |-> nextValue;
{
    open nodes(before, first, last, after, values);
    if (first == after) {
        close nodes(after, next, after, next, nil);
        close nodes(last, after, after, next, {value});
    } else {
        deque_add();
        close nodes(before, first, after, next, append(values, {value}));
    }
}

@*/

void push_back(struct Node *deque, int32_t value)
//@ requires deque(deque, ?values);
//@ ensures deque(deque, append(values, {value}));
{
    //@ open deque(_, _);
    //@ bool empty = deque->next == deque;
    /*@
    if (empty) {
        open nodes(deque, _, _, _, _);
    } else {
        deque_snoc();
    }
    @*/
    struct Node *n = malloc(sizeof(struct Node));
    if (n == 0) abort();
    (*n).prev = (*deque).prev;
    (*n).value = value;
    (*n).next = deque;
    (*(*n).prev).next = n;
    (*(*n).next).prev = n;
    /*@
    if (empty) {
    } else {
        deque_add();
        deque_add();
    }
    @*/
}

bool is_empty(struct Node *deque)
//@ requires deque(deque, ?values);
//@ ensures deque(deque, values) &*& result == (values == nil);
{
    //@ open deque(deque, values);
    //@ open nodes(?before, ?first, ?last, ?after, values);
    return (*deque).next == deque;
}

int32_t pop_front(struct Node *deque)
//@ requires deque(deque, cons(?value, ?values));
//@ ensures deque(deque, values) &*& result == value;
{
    struct Node *n = (*deque).next;
    //@ open nodes(deque, n, ?last, deque, _);
    int32_t result = (*n).value;
    (*(*n).prev).next = (*n).next;
    //@ open nodes(n, ?next, last, deque, _);
    (*(*n).next).prev = (*n).prev;
    free(n);
    return result;
}

int32_t pop_back(struct Node *deque)
//@ requires deque(deque, ?values) &*& values != nil;
//@ ensures deque(deque, ?values1) &*& values == append(values1, {result});
{
    struct Node *n = (*deque).prev;
    //@ open nodes(deque, ?first, ?last, ?after, values);
    //@ close nodes(deque, first, last, after, values);
    //@ deque_snoc();
    int32_t result = (*n).value;
    //@ bool empty = deque->next == n;
    /*@
    if (empty) {
        open nodes(deque, first, _, _, _);
    } else {
        deque_snoc();
    }
    @*/
    (*(*n).prev).next = (*n).next;
    (*(*n).next).prev = (*n).prev;
    /*@
    if (empty) {
    } else {
        deque_add();
    }
    @*/
    free(n);
    return result;
}

void drop_deque(struct Node *deque)
//@ requires deque(deque, nil);
//@ ensures true;
{
    free(deque);
    //@ open nodes(_, _, _, _, _);
}

void assert_(bool b)
//@ requires b;
//@ ensures true;
{
    if (!b)
        abort();
}

/*@

lemma void note(bool b)
    requires b;
    ensures b;
{}

@*/

void main_()
//@ requires true;
//@ ensures true;
{
    struct Node *deque = create_deque();
    assert_(is_empty(deque));
    push_front(deque, 10);
    assert_(!is_empty(deque));
    push_back(deque, 20);
    push_front(deque, 30);
    push_back(deque, 40);
    assert_(pop_front(deque) == 30);
    //@ append_take_drop_n({10, 20, 40}, 2);
    //@ assert deque(deque, ?values) &*& values == {10, 20, 40};
    //@ note(drop(2, {10, 20, 40}) == {40});
    int32_t e2 = pop_back(deque);
    //@ assert deque(deque, ?values1) &*& values == append(values1, {e2});
    //@ note(length(values1) == 2);
    //@ drop_append(2, values1, {e2});
    assert_(e2 == 40);
    assert_(pop_front(deque) == 10);
    int32_t e4 = pop_back(deque);
    //@ assert deque(deque, ?values3);
    //@ switch (values3) { case nil: case cons(h, t): }
    assert_(e4 == 20);
    drop_deque(deque);
}

int main()
//@ requires true;
//@ ensures true;
{
    main_();
    return 0;
}
