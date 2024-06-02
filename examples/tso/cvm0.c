// tab_size:4

#include <stdio.h>
#include <stdlib.h>
#include "tso.h"
//@ #include "listex.gh"

typedef struct object *object;

/*@

predicate_ctor object(list<object> os)(void *o) =
    [_]object_class(o, ?c) &*&
    [_]c->inv |-> ?inv &*&
    [_]c->print |-> ?print &*&
    inv(o, ?os0) &*& subset(os0, os) == true &*&
    [_]is_print_func(print, c);

predicate classes() =
    class_inv(&cell_class, cell_inv) &*&
    class_print(&cell_class, print_cell) &*&
    [_]is_print_func(print_cell, &cell_class) &*&
    class_inv(&interval_class, interval_inv) &*&
    class_print(&interval_class, print_interval) &*&
    [_]is_print_func(print_interval, &interval_class) &*&
    emp;

predicate heap(list<struct object *> objects) =
    [_]classes() &*& foreach(objects, object(objects));

fixpoint void *get_vararg_as_pointer(vararg a) {
    switch (a) {
        case vararg_pointer(x): return x;
        default: return (void *)0;
    }
}

fixpoint b idf<a, b>(a a, b b) { return b; }

fixpoint list<object> consf(list<vararg> args, list<object> os) { return cons(get_vararg_as_pointer(head(args)), os); }

fixpoint list<object> constf(list<vararg> args, list<object> dummy) { return cons(get_vararg_as_pointer(head(args)), nil); }

predicate mytso(int id, list<object> os) = tso(id, heap, subset, cons(idf, cons(consf, cons(constf, nil))), os);

@*/

struct class;

struct object {
    struct class *class;
};

typedef void print_func/*@(struct class *c)@*/(struct object *o);
    //@ requires [_]classes() &*& [_]o->class |-> c &*& [?f]mytso(?id, ?objects) &*& mem(o, objects) == true;
    //@ ensures [f]mytso(id, objects);

struct class {
    print_func *print;
    //@ predicate(void *, list<struct object *>) inv;
};

void print_object(struct object *o)
    //@ requires [_]classes() &*& [?f]mytso(?id, ?objects) &*& mem(o, objects) == true;
    //@ ensures [f]mytso(id, objects);
{
    {
        /*@
        predicate P() = true;
        predicate Q() = [_]o->class |-> ?c &*& [_]c->print |-> ?print &*& [_]is_print_func(print, c);
        lemma void body(list<object> os0, list<object> os1)
            requires P() &*& subset(objects, os0) == true &*& subset(os0, os1) == true &*& heap(os1);
            ensures Q() &*& heap(os1) &*& subset(os1, os1) == true &*& subset(os0, os1) == true;
        {
            open P();
            open heap(_);
            subset_trans(objects, os0, os1);
            mem_subset(o, objects, os1);
            foreach_remove(o, os1);
            open object(os1)(o);
            close Q();
            close object(os1)(o);
            foreach_unremove(o, os1);
            close heap(os1);
        }
        @*/
        //@ produce_lemma_function_pointer_chunk(body) : tso_noop_body<list<object> >(heap, subset, objects, (idf)(nil), P, Q)(os0, os1) { call(); };
        //@ close P();
        //@ open mytso(_, _);
        tso_noop(0);
        //@ close [f]mytso(id, objects);
        //@ open Q();
    }
    print_func *print = o->class->print;
    print(o);
}

struct cell {
    struct object object;
    struct object *contents;
};

//@ predicate cell_inv(void *cell, list<object> os) = ((struct cell *)cell)->contents |-> ?contents &*& mem(contents, os) == true &*& struct_cell_padding(cell) &*& struct_object_padding(cell);

void get_cell_properties(void *cell)
    //@ requires [_]classes() &*& [_]object_class(cell, &cell_class) &*& [?f]mytso(?id, ?objects) &*& mem(cell, objects) == true;
    //@ ensures [f]mytso(id, objects) &*& pointer_within_limits(&((struct cell *)cell)->contents) == true;
{
    struct cell *cell_ = cell;
    {
        /*@
        predicate P() = [_]classes() &*& [_]object_class(cell, &cell_class);
        predicate Q() = pointer_within_limits(&cell_->contents) == true;
        lemma void body(list<object> os0, list<object> os1)
            requires P() &*& subset(objects, os0) == true &*& subset(os0, os1) == true &*& heap(os1);
            ensures Q() &*& heap(os1) &*& subset(os1, os1) == true &*& subset(os0, os1) == true;
        {
            open P();
            open heap(_);
            subset_trans(objects, os0, os1);
            mem_subset(cell, objects, os1);
            foreach_remove(cell, os1);
            open object(os1)(cell);
            open classes();
            open cell_inv(cell, ?os00);
            close cell_inv(cell, os00);
            close Q();
            close object(os1)(cell);
            foreach_unremove(cell, os1);
            close heap(os1);
        }
        @*/
        //@ produce_lemma_function_pointer_chunk(body) : tso_noop_body<list<object> >(heap, subset, objects, (idf)(nil), P, Q)(os0, os1) { call(); };
        //@ close P();
        //@ open mytso(_, _);
        tso_noop(0);
        //@ close [f]mytso(id, objects);
        //@ open Q();
    }
}

void *read_cell_contents0(void *cell)
    //@ requires [_]classes() &*& [_]object_class(cell, &cell_class) &*& [?f]mytso(?id, cons(cell, nil));
    //@ ensures [f]mytso(id, cons(result, nil));
{
    struct cell *cell_ = cell;
    get_cell_properties(cell);
    prophecy_id contents0Id = create_tso_prophecy();
    //@ assert tso_prophecy(contents0Id, ?contents0);
    struct object *contents;
    {
        /*@
        predicate P() = object_class(cell, &cell_class);
        lemma void ctxt(list<object> os)
            requires subset(cons(cell, nil), os) == true &*& heap(os) &*& is_tso_read_op(?op, &cell_->contents, contents0, ?pre, ?post) &*& pre() &*& [_]P();
            ensures heap(os) &*& subset(cons(contents0, nil), os) == true &*& post() &*& is_tso_read_op(op, &cell_->contents, contents0, pre, post);
        {
            open heap(os);
            foreach_remove(cell, os);
            open object(os)(cell);
            open P();
            open classes();
            open cell_inv(cell, ?os0);
            op();
            mem_subset(contents0, os0, os);
            close cell_inv(cell, os0);
            close object(os)(cell);
            foreach_unremove(cell, os);
            close heap(os);
        }
        @*/
        //@ produce_lemma_function_pointer_chunk(ctxt) : tso_read_ctxt<list<object> >(&cell_->contents, contents0, heap, subset, cons(cell, nil), cons(contents0, nil), P)(os) { call(); };
        //@ assert [?f1]object_class(cell, _);
        //@ close [f1]P();
        //@ open [f]mytso(id, _);
        contents = tso_read(contents0Id, &cell_->contents, 2, cell);
        //@ close [f]mytso(id, cons(contents0, nil));
    }
    return contents;
}

//@ predicate mytso_wrapper(int id, list<object> objects) = mytso(id, objects);

void *read_cell_contents(void *cell)
    //@ requires [_]classes() &*& [_]object_class(cell, &cell_class) &*& [?f]mytso(?id, ?objects) &*& mem(cell, objects) == true;
    //@ ensures [f]mytso(id, cons(result, objects));
{
    //@ close [f/2]mytso_wrapper(id, objects);
    //@ open mytso(_, _);
    //@ tso_weaken(cons(cell, nil));
    //@ close [f/2]mytso(id, cons(cell, nil));
    void *result = read_cell_contents0(cell);
    //@ open mytso(_, _);
    //@ open mytso_wrapper(_, _);
    //@ open mytso(_, _);
    //@ tso_merge();
    //@ tso_weaken(cons(result, objects));
    //@ close [f]mytso(id, cons(result, objects));
    return result;
}

void print_cell(void *cell)
    //@ requires [_]classes() &*& [_]object_class(cell, &cell_class) &*& [?f]mytso(?id, ?objects) &*& mem(cell, objects) == true;
    //@ ensures [f]mytso(id, objects);
{
    void *contents = read_cell_contents(cell);
    print_object(contents);
    //@ subset_cons(contents, objects);
    //@ open mytso(_, _);
    //@ tso_weaken(objects);
    //@ close [f]mytso(id, objects);
}

struct class cell_class = {print_cell};

struct interval {
    struct object object;
    int a;
    int b;
};

//@ predicate interval_inv(void *interval, list<object> os) = [_]interval_a(interval, _) &*& [_]interval_b(interval, _) &*& struct_interval_padding(interval) &*& struct_object_padding(interval);

void print_interval(void *interval)
    //@ requires [_]classes() &*& [_]object_class(interval, &interval_class) &*& [?f]mytso(?id, ?objects) &*& mem(interval, objects) == true;
    //@ ensures [f]mytso(id, objects);
{
    struct interval *interval_ = interval;
    {
        /*@
        predicate P() = [_]object_class(interval, &interval_class);
        predicate Q() = [_]interval_->a |-> ?a &*& [_]interval_->b |-> ?b;
        lemma void body(list<object> os1, list<object> os)
            requires P() &*& subset(objects, os1) == true &*& subset(os1, os) == true &*& heap(os);
            ensures Q() &*& heap(os) &*& subset(os, os) == true &*& subset(os1, os) == true;
        {
            open P();
            open heap(os);
            subset_trans(objects, os1, os);
            mem_subset(interval, objects, os);
            foreach_remove(interval, os);
            open object(os)(interval);
            open classes();
            open interval_inv(interval, ?os0);
            close interval_inv(interval, os0);
            close object(os)(interval);
            foreach_unremove(interval, os);
            close heap(os);
            close Q();
        }
        @*/
        //@ produce_lemma_function_pointer_chunk(body) : tso_noop_body<list<object> >(heap, subset, objects, (idf)(nil), P, Q)(os1, os) { call(); };
        //@ close P();
        //@ open mytso(_, _);
        tso_noop(0);
        //@ close [f]mytso(id, objects);
        //@ open Q();
    }
    printf("(%d, %d)\n", interval_->a, interval_->b);
}

struct class interval_class = {print_interval};

#define HEAP_SIZE 10000

char heap_[HEAP_SIZE];
char *heap_free_space;

//@ predicate free_space(;) = pointer(&heap_free_space, ?fs) &*& fs >= (char *)heap_ &*& fs == heap_ + ((char *)fs - heap_) &*& chars(fs, (char *)heap_ + HEAP_SIZE - (char *)fs, _);

void *heap_alloc(size_t size)
    //@ requires free_space() &*& 0 <= size;
    //@ ensures free_space() &*& chars(result, size, _);
{
    //@ open free_space();
    char *fs = heap_free_space;
    //@ produce_limits(fs);
    //@ chars_limits(fs);
    if (size > (unsigned int) INT_MAX) abort();
    if (heap_ + HEAP_SIZE - fs < (int)size) abort();
    heap_free_space += (int)size;
    return fs;
    //@ chars_split(fs, size);
}

struct cell *create_cell(struct object *contents)
    //@ requires free_space();
    //@ ensures free_space() &*& [_]object_class(&result->object, &cell_class) &*& cell_inv(result, cons(contents, nil));
{
    struct cell *cell = heap_alloc(sizeof(struct cell));
    //@ close_struct(cell);
    (&cell->object)->class = &cell_class;
    cell->contents = contents;
    return cell;
    //@ leak object_class(&cell->object, _);
    //@ close cell_inv(cell, cons(contents, nil));
}

struct interval *create_interval(int a, int b)
    //@ requires free_space();
    //@ ensures free_space() &*& [_]object_class(&result->object, &interval_class) &*& interval_inv(result, nil);
{
    struct interval *interval = heap_alloc(sizeof(struct interval));
    //@ close_struct(interval);
    (&interval->object)->class = &interval_class;
    interval->a = a;
    interval->b = b;
    return interval;
    //@ leak object_class(&interval->object, _) &*& interval->a |-> ?a_ &*& interval->b |-> ?b_;
    //@ close interval_inv(interval, nil);
}

/*@

lemma void foreach_object_cons(list<object> os1, object o, list<object> os)
    requires foreach(os1, object(os));
    ensures foreach(os1, object(cons(o, os)));
{
    open foreach(_, _);
    switch (os1) {
        case nil:
        case cons(o0, os0):
            open object(os)(o0);
            assert [_]object_class(o0, ?c0) &*& [_]c0->inv |-> ?inv0 &*& inv0(o0, ?os00);
            subset_cons(o, os);
            subset_trans(os00, os, cons(o, os));
            close object(cons(o, os))(o0);
            foreach_object_cons(os0, o, os);
    }
    close foreach(os1, object(cons(o, os)));
}

@*/

void tso_add_object(void *o)
    //@ requires [?f]mytso(?id, ?objects) &*& [_]object_class(o, ?c) &*& [_]c->inv |-> ?inv &*& [_]c->print |-> ?print &*& inv(o, ?os) &*& subset(os, objects) == true &*& [_]is_print_func(print, c);
    //@ ensures [f]mytso(id, cons(o, objects));
{
    {
        /*@
        predicate P() = [_]object_class(o, c) &*& [_]c->inv |-> inv &*& [_]c->print |-> print &*& inv(o, os) &*& subset(os, objects) == true &*& [_]is_print_func(print, c);
        predicate Q() = true;
        lemma void body(list<object> os0, list<object> os1)
            requires P() &*& subset(objects, os0) == true &*& subset(os0, os1) == true &*& heap(os1);
            ensures Q() &*& heap(cons(o, os1)) &*& subset(os1, cons(o, os1)) == true &*& subset(cons(o, os0), cons(o, os1)) == true;
        {
            open P();
            open heap(os1);
            subset_trans(objects, os0, os1);
            subset_trans(os, objects, os1);
            subset_cons(o, os1);
            subset_trans(os, os1, cons(o, os1));
            close object(cons(o, os1))(o);
            foreach_object_cons(os1, o, os1);
            close Q();
            close foreach(cons(o, os1), object(cons(o, os1)));
            close heap(cons(o, os1));
            subset_trans(os0, os1, cons(o, os1));
        }
        @*/
        //@ produce_lemma_function_pointer_chunk(body) : tso_noop_body<list<object> >(heap, subset, objects, (consf)(cons(vararg_pointer(o), nil)), P, Q)(os0, os1) { call(); };
        //@ close P();
        //@ open mytso(_, _);
        tso_noop(1, o);
        //@ close [f]mytso(id, cons(o, objects));
        //@ open Q();
    }
}

void write_cell_contents(struct cell *cell, void *contents)
    //@ requires [_]classes() &*& [?f]mytso(?id, ?objects) &*& mem<void *>(cell, objects) == true &*& mem(contents, objects) == true &*& [_]object_class(&cell->object, &cell_class);
    //@ ensures [f]mytso(id, objects);
{
    get_cell_properties(cell);
    {
        /*@
        predicate P() = [_]object_class(&cell->object, &cell_class);
        predicate Q() = emp;
        lemma void ctxt(list<object> os1, list<object> os)
            requires P() &*& subset(objects, os1) == true &*& subset(os1, os) == true &*& heap(os) &*& is_tso_write_op(?op, &cell->contents, contents, ?pre, ?post) &*& pre();
            ensures Q() &*& heap(os) &*& subset(os, os) == true &*& subset(os1, os) == true &*& post() &*& is_tso_write_op(op, &cell->contents, contents, pre, post);
        {
            open P();
            open heap(os);
            subset_trans(objects, os1, os);
            mem_subset<void *>(cell, objects, os);
            foreach_remove<void *>(cell, os);
            open object(os)(cell);
            open classes();
            open cell_inv(cell, ?os0);
            op();
            close cell_inv(cell, cons(contents, nil));
            mem_subset(contents, objects, os);
            close object(os)(cell);
            foreach_unremove<void *>(cell, os);
            close heap(os);
            close Q();
        }
        @*/
        //@ produce_lemma_function_pointer_chunk(ctxt) : tso_write_ctxt<list<object> >(&cell->contents, contents, heap, subset, objects, (idf)(nil), P, Q)(os1, os) { call(); };
        //@ close P();
        //@ open mytso(_, _);
        tso_write(&cell->contents, contents, 0);
        //@ close [f]mytso(id, objects);
        //@ open Q();
    }
}

struct cell *cell;

void producer()
    //@ requires [_]classes() &*& free_space() &*& pointer(&cell, ?cell_) &*& [1/2]mytso(?id, ?objects0) &*& mem(cell_, objects0) == true &*& [_]object_class(cell_, &cell_class);
    //@ ensures [_]classes() &*& free_space() &*& pointer(&cell, cell_) &*& [1/2]mytso(id, ?objects1) &*& mem(cell_, objects1) == true &*& [_]object_class(cell_, &cell_class);
{
    for (;;)
        //@ invariant [_]classes() &*& free_space() &*& pointer(&cell, cell_) &*& [1/2]mytso(id, ?objects2) &*& mem(cell_, objects2) == true &*& [_]object_class(cell_, &cell_class);
    {
        //@ open classes();
        struct interval *interval = create_interval(0, 0);
        tso_add_object(interval);
        write_cell_contents(cell, interval);
    }
}

void consumer()
    //@ requires [_]classes() &*& pointer(&cell, ?cell_) &*& [1/2]mytso(?id, ?objects0) &*& mem(cell_, objects0) == true &*& [_]object_class(cell_, &cell_class);
    //@ ensures [_]classes() &*& pointer(&cell, cell_) &*& [1/2]mytso(id, ?objects1) &*& mem(cell_, objects1) == true &*& [_]object_class(cell_, &cell_class);
{
    for (;;)
        //@ invariant [_]classes() &*& pointer(&cell, cell_) &*& [1/2]mytso(id, ?objects2) &*& mem(cell_, objects2) == true &*& [_]object_class(cell_, &cell_class);
    {
        struct object *object = read_cell_contents(cell);
        print_object(object);
    }
}

void init()
    //@ requires module(cvm0, true);
    //@ ensures [_]classes() &*& free_space() &*& pointer(&cell, 0) &*& mytso(_, nil);
{
    //@ open_module();
    
    //@ cell_class.inv = cell_inv;
    //@ produce_function_pointer_chunk print_func(print_cell)(&cell_class)(o) { call(); }
    //@ interval_class.inv = interval_inv;
    //@ produce_function_pointer_chunk print_func(print_interval)(&interval_class)(o) { call(); }
    //@ close classes();
    //@ leak classes();
    
    heap_free_space = heap_;
    //@ close free_space();
    
    //@ close foreach(nil, object(nil));
    //@ close heap(nil);
    {
        /*@
        lemma void subset_refl_(list<object> os)
            requires true;
            ensures subset(os, os) == true;
        {
            subset_refl(os);
        }
        lemma void subset_trans_(list<object> os1, list<object> os2, list<object> os3)
            requires subset(os1, os2) && subset(os2, os3);
            ensures subset(os1, os3) == true;
        {
            subset_trans(os1, os2, os3);
        }
        @*/
        //@ produce_lemma_function_pointer_chunk(subset_refl_) : le_refl<list<object> >(subset)(os) { call(); };
        //@ produce_lemma_function_pointer_chunk(subset_trans_) : le_trans<list<object> >(subset)(os1, os2, os3) { call(); };
        //@ int id = create_tso(heap, subset, cons(idf, cons(consf, cons(constf, nil))), nil);
        //@ close mytso(id, nil);
    }
}

int main()
    //@ requires module(cvm0, true);
    //@ ensures true;
{
    init();
    //@ open classes();
    
    struct interval *interval0 = create_interval(0, 0);
    tso_add_object(interval0);
    
    cell = create_cell(&interval0->object);
    tso_add_object(cell);
    
    /*fork*/ consumer();
    producer();
    
    //@ open mytso(_, _);
    //@ open mytso(_, _);
    //@ tso_merge();
    //@ tso_destroy();
    //@ assert heap(_);
    
    abort();
}
