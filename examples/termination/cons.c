#include <stdlib.h>
//@ #include "termination.gh"

/*@

predicate list_object(list_object object; void *contains, void *intersects, predicate(list_object; list<void *>) p, list<void *> d) =
    object->contains |-> contains &*&
    object->intersects |-> intersects &*&
    object->p |-> p &*&
    object->d |-> d &*&
    [_]is_contains(contains, p) &*&
    [_]is_intersects(intersects, p) &*&
    p(object, ?d_) &*&
    bag_le(func_lt, cons(contains, cons(intersects, d_)), d) == true;

@*/

typedef bool contains/*@(predicate(list_object; list<void *>) p)@*/(list_object object, int element);
    //@ requires [?f]list_object(object, this, ?intersects, p, ?d) &*& call_perm(currentThread, d);
    //@ ensures [f]list_object(object, this, intersects, p, d);
    //@ terminates;

typedef bool intersects/*@(predicate(list_object; list<void *>) p)@*/(list_object object, list_object other);
    //@ requires [?f]list_object(object, ?contains, this, p, ?d) &*& [?f_other]list_object(other, _, _, ?p_other, ?d_other) &*& call_perm(currentThread, append(d, d_other));
    //@ ensures [f]list_object(object, contains, this, p, d) &*& [f_other]list_object(other, _, _, p_other, d_other);
    //@ terminates;

struct list_object {
    contains *contains;
    intersects *intersects;
    //@ predicate(list_object; list<void *>) p;
    //@ list<void *> d;
};
typedef struct list_object *list_object;

bool list_object_contains(list_object object, int element)
    //@ requires [?f]list_object(object, _, _, ?p, ?d) &*& call_perm_below(currentThread, ?d1) &*& func_bag_lt(cons(list_object_contains, d), d1) == true;
    //@ ensures [f]list_object(object, _, _, p, d);
    //@ terminates;
{
    //@ open [f]list_object(object, _, ?intersects, p, d);
    contains *contains = object->contains;
    //@ assert [f]p(object, ?d_);
    //@ close [f]list_object(object, contains, intersects, p, d);
    //@ call_perm(cons(list_object_contains, d));
    //@ call_perm_below(2);
    //@ bag_lt_xs_cons_xs(func_lt, list_object_contains, d);
    //@ call_perm(d);
    //@ is_order_func_lt();
    //@ bag_le_cons_xs_cons_ys(func_lt, contains, nil, cons(intersects, d_));
    //@ bag_le_bag_lt(func_lt, cons(contains, cons(intersects, d_)), d, cons(list_object_contains, d));
    //@ bag_le_bag_lt(func_lt, {contains}, cons(contains, cons(intersects, d_)), cons(list_object_contains, d));
    //@ consume_call_perm_for(contains);
    return contains(object, element);
}

bool list_object_intersects(list_object object, list_object other)
    //@ requires [?f]list_object(object, _, _, ?p, ?d) &*& [?f_other]list_object(other, _, _, ?p_other, ?d_other) &*& call_perm_below(currentThread, ?d1) &*& func_bag_lt(cons(list_object_intersects, append(d, d_other)), d1) == true;
    //@ ensures [f]list_object(object, _, _, p, d) &*& [f_other]list_object(other, _, _, p_other, d_other);
    //@ terminates;
{
    //@ open [f]list_object(object, ?contains, _, p, d);
    intersects *intersects = object->intersects;
    //@ assert [f]p(object, ?d_);
    //@ close [f]list_object(object, contains, _, p, d);
    //@ call_perm(cons(list_object_intersects, append(d, d_other)));
    //@ call_perm_below(2);
    //@ bag_lt_xs_cons_xs(func_lt, list_object_intersects, append(d, d_other));
    //@ call_perm(append(d, d_other));
    //@ is_order_func_lt();
    //@ bag_lt_xs_cons_xs(func_lt, contains, cons(intersects, append(d_, d_other)));
    //@ bag_le_cons_xs_cons_ys(func_lt, intersects, nil, append(d_, d_other));
    //@ bag_le_trans(func_lt, {intersects}, cons(intersects, append(d_, d_other)), cons(contains, cons(intersects, append(d_, d_other))));
    //@ bag_le_cons_xs_cons_ys(func_lt, intersects, nil, d_);
    //@ bag_le_bag_le_append_l(func_lt, cons(contains, cons(intersects, d_)), d, d_other);
    //@ bag_le_bag_lt(func_lt, cons(contains, cons(intersects, append(d_, d_other))), append(d, d_other), cons(list_object_intersects, append(d, d_other)));
    //@ bag_le_bag_lt(func_lt, {intersects}, cons(contains, cons(intersects, append(d_, d_other))), cons(list_object_intersects, append(d, d_other)));
    //@ consume_call_perm_for(intersects);
    return intersects(object, other);
}

/*@

predicate nil(list_object object; list<void *> d) =
    malloc_block_list_object(object) &*& d == nil;

@*/

bool nil_contains(list_object object, int element)
    //@ requires [?f]list_object(object, nil_contains, ?intersects, @nil, ?d) &*& call_perm(currentThread, d);
    //@ ensures [f]list_object(object, nil_contains, intersects, @nil, d);
    //@ terminates;
{
    return false;
    //@ leak call_perm(currentThread, d);
}

bool nil_intersects(list_object object, list_object other)
    //@ requires [?f]list_object(object, ?contains, nil_intersects, @nil, ?d) &*& [?f_other]list_object(other, _, _, ?p_other, ?d_other) &*& call_perm(currentThread, append(d, d_other));
    //@ ensures [f]list_object(object, contains, nil_intersects, @nil, d) &*& [f_other]list_object(other, _, _, p_other, d_other);
    //@ terminates;
{
    return false;
    //@ leak call_perm(currentThread, append(d, d_other));
}

list_object create_nil()
    //@ requires call_perm_below(currentThread, ?d1) &*& func_bag_lt({create_nil}, d1) == true;
    //@ ensures list_object(result, _, _, _, {create_nil});
    //@ terminates;
{
    list_object object = malloc(sizeof(struct list_object));
    if (object == 0) abort();
    object->contains = nil_contains;
    object->intersects = nil_intersects;
    //@ object->p = @nil;
    //@ object->d = {create_nil};
    return object;
    //@ produce_function_pointer_chunk contains(nil_contains)(@nil)(object_, element) { call(); }
    //@ produce_function_pointer_chunk intersects(nil_intersects)(@nil)(object_, other) { call(); }
    //@ close nil(object, nil);
    //@ close list_object(object, nil_contains, nil_intersects, @nil, {create_nil});
    //@ leak call_perm_below(currentThread, _);
}

struct cons {
    struct list_object object;
    int head;
    list_object tail;
};
typedef struct cons *cons;

/*@

predicate cons(list_object object; list<void *> d) =
    cons_head((void *)object, ?head) &*&    
    cons_tail((void *)object, ?tail) &*& list_object(tail, _, _, _, d) &*&
    malloc_block_cons((void *)object);

@*/

bool cons_contains(list_object object, int element)
    //@ requires [?f]list_object(object, cons_contains, ?intersects, @cons, ?d) &*& call_perm(currentThread, d);
    //@ ensures [f]list_object(object, cons_contains, intersects, @cons, d);
    //@ terminates;
{
    //@ open [f]list_object(object, cons_contains, intersects, @cons, d);
    //@ open [f]cons(object, ?dc);
    //@ call_perm_weaken(cons(cons_contains, cons(intersects, dc)));
    //@ call_perm_below(1);
    cons c = (void *)object;
    bool result;
    if (c->head == element) {
        result = true;
        //@ leak call_perm_below(currentThread, _);
    } else {
        list_object tail = c->tail;
        //@ bag_lt_xs_cons_xs(func_lt, cons_contains, cons(intersects, dc));
        //@ bag_lt_xs_cons_xs(func_lt, intersects, dc);
        //@ is_order_func_lt();
        //@ bag_le_cons_xs_cons_ys(func_lt, list_object_contains, dc, cons(intersects, dc));
        //@ bag_lt_cons_lt(func_lt, list_object_contains, cons_contains, cons(intersects, dc));
        //@ bag_le_bag_lt(func_lt, cons(list_object_contains, dc), cons(list_object_contains, cons(intersects, dc)), cons(cons_contains, cons(intersects, dc)));
        result = list_object_contains(tail, element);
    }
    return result;
    //@ close [f]cons(object, dc);
    //@ close [f]list_object(object, cons_contains, intersects, @cons, d);
}

bool cons_intersects(list_object object, list_object other)
    //@ requires [?f]list_object(object, ?contains, cons_intersects, @cons, ?d) &*& [?f_other]list_object(other, _, _, ?p_other, ?d_other) &*& call_perm(currentThread, append(d, d_other));
    //@ ensures [f]list_object(object, contains, cons_intersects, @cons, d) &*& [f_other]list_object(other, _, _, p_other, d_other);
    //@ terminates;
{
    //@ open [f]list_object(object, contains, cons_intersects, @cons, d);
    //@ open cons(object, ?dc);
    //@ bag_le_bag_le_append_l(func_lt, cons(contains, cons(cons_intersects, dc)), d, d_other);
    //@ call_perm_weaken(append(cons(contains, cons(cons_intersects, dc)), d_other));
    //@ call_perm_below(2);
    cons c = (void *)object;
    bool result;
    //@ bag_le_append_r(func_lt, cons(cons_intersects, dc), d_other);
    //@ bag_lt_xs_cons_xs(func_lt, contains, append(cons(cons_intersects, dc), d_other));
    //@ is_order_func_lt();
    //@ bag_le_append_r(func_lt, dc, d_other);
    //@ bag_le_cons_xs_cons_ys(func_lt, list_object_contains, d_other, append(dc, d_other));
    //@ bag_lt_cons_lt(func_lt, list_object_contains, cons_intersects, append(dc, d_other));
    //@ bag_le_trans(func_lt, cons(list_object_contains, d_other), cons(list_object_contains, append(dc, d_other)), cons(cons_intersects, append(dc, d_other)));
    //@ bag_le_bag_lt(func_lt, cons(list_object_contains, d_other), append(cons(cons_intersects, dc), d_other), append(cons(contains, cons(cons_intersects, dc)), d_other));
    if (list_object_contains(other, c->head)) {
        result = true;
        //@ leak call_perm_below(currentThread, _);
    } else {
        //@ bag_lt_xs_cons_xs(func_lt, contains, append(cons(cons_intersects, dc), d_other));
        //@ bag_lt_cons_lt(func_lt, list_object_intersects, cons_intersects, append(dc, d_other));
        //@ bag_le_bag_lt(func_lt, cons(list_object_intersects, append(dc, d_other)), cons(cons_intersects, append(dc, d_other)), append(cons(contains, cons(cons_intersects, dc)), d_other));
        result = list_object_intersects(c->tail, other);
    }
    return result;
    //@ close [f]cons(object, dc);
    //@ close [f]list_object(object, contains, cons_intersects, @cons, d);
}

cons create_cons(int head, list_object tail)
    //@ requires list_object(tail, _, _, _, ?d_tail) &*& call_perm_below(currentThread, ?d1) &*& func_bag_lt(cons(create_cons, d_tail), d1) == true;
    //@ ensures list_object((void *)result, _, _, _, cons(create_cons, d_tail));
    //@ terminates;
{
    cons c = malloc(sizeof(struct cons));
    if (c == 0) abort();
    c->object.contains = cons_contains;
    c->object.intersects = cons_intersects;
    c->head = head;
    c->tail = tail;
    return c;
    //@ c->object.p = @cons;
    //@ c->object.d = cons(create_cons, d_tail);
    //@ produce_function_pointer_chunk contains(cons_contains)(@cons)(object, element) { call(); }
    //@ produce_function_pointer_chunk intersects(cons_intersects)(@cons)(object, other) { call(); }
    //@ close cons((void *)c, d_tail);
    //@ bag_le_bag_le_append_l(func_lt, {cons_contains, cons_intersects}, {create_cons}, d_tail);
    //@ close list_object((void *)c, cons_contains, cons_intersects, @cons, cons(create_cons, d_tail));
    //@ leak call_perm_below(currentThread, d1);
}

int main() //@ : main
    //@ requires true;
    //@ ensures true;
    //@ terminates;
{
    //@ produce_call_below_perm_();
    //@ call_below_perm__elim(main);
    //@ produce_call_below_perm_();
    //@ call_below_perm__elim(main);
    //@ produce_call_below_perm_();
    //@ call_below_perm__elim(main);
    //@ produce_call_below_perm_();
    //@ call_below_perm__elim(main);
    //@ produce_call_below_perm_();
    //@ call_below_perm__elim(main);
    //@ produce_call_below_perm_();
    //@ call_below_perm__elim(main);
    //@ produce_call_below_perm_();
    //@ call_below_perm__elim(main);
    //@ produce_call_below_perm_();
    //@ call_below_perm__elim(main);
    //@ produce_call_below_perm_();
    //@ call_below_perm__elim(main);
    //@ produce_call_below_perm_();
    //@ call_below_perm__elim(main);
    
    void *l = create_nil();
    l = create_cons(3, l);
    l = create_cons(2, l);
    l = create_cons(1, l);
    list_object_contains(l, 2);
    //@ split_fraction list_object(l, _, _, _, _);
    list_object_intersects(l, l);
    void *l2 = create_nil();
    l2 = create_cons(2, l2);
    l2 = create_cons(4, l2);
    list_object_intersects(l, l2);
    //@ leak list_object(l, _, _, _, _);
    //@ leak list_object(l2, _, _, _, _);
    return 0;
}