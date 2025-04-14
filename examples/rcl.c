/*

An interpreter for a minimalist Reference-Counted Language.

Reads expressions from standard input and executes them.

Syntax:

EXPR ::= ATOM               variable lookup
       | (EXPR EXPR)        function application
       | (fun (PARAM BODY)) lambda expression
       | (quote EXPR)       evaluates to EXPR itself

Currently, there is just one built-in function: 'print_atom'.

Examples:

    (print_atom (quote Hello_world!))
 => Hello_world!

    ((fun (iter (iter iter)))
     (fun (iter ((fun (v (iter iter))) (print_atom (quote Hello))))))
 => HelloHelloHelloHello...

To compile (with MSVC):

    cl rcl.c tokenizer.c stringBuffers.c

Performs tail call optimization. Also: does not use the C stack
(i.e. the C program performs no recursion), so recursion depth is
limited only by available memory and no C stack overflows can
happen.

Memory safety of the interpreter has been verified using VeriFast. It follows
that it is relatively safe to run untrusted code with this interpreter.

*/


#include <stdlib.h>
#include <stdio.h>
#include "stringBuffers.h"
#include "tokenizer.h"
//@ #include "ghostlist.gh"
//@ #include "counting.gh"

void error(char *msg)
    //@ requires [?f]string(msg, ?cs);
    //@ ensures false;
{
    puts(msg);
    abort();
}

typedef void dispose_func/*@(predicate(void *) inv)@*/(struct object *object);
    //@ requires heap0(nil) &*& object->refCount |-> ?refCount &*& object->class |-> ?class &*& inv(object);
    //@ ensures heap0(nil);

struct class {
    char *name;
    //@ predicate(void *) inv;
    dispose_func *dispose;
};

struct object {
    int refCount;
    struct class *class;
};

struct globals {
    int dummy;
    //@ int objectListId;
};

struct globals globals;

/*@

predicate object_ticket_base(struct object *object; struct class *class) =
    object->class |-> class &*& [_]globals_objectListId(&globals, ?id) &*& ghost_list_member_handle(id, object);

predicate object_refcount(struct object *object) =
    object->refCount |-> ?refCount &*& 0 < refCount &*& counting(object_ticket_base, object, refCount + 1, _);

predicate object_inv(struct object *object) =
    ticket(object_ticket_base, object, ?f) &*& [f]object->class |-> ?class &*&
    [_]globals_objectListId(&globals, ?id) &*& [f]ghost_list_member_handle(id, object) &*&
    [_]class->dispose |-> ?dispose &*&
    [_]class->inv |-> ?inv &*& inv(object) &*&
    [_]is_dispose_func(dispose, inv);

fixpoint bool sublist<t>(list<t> xs, list<t> ys) {
    switch (xs) {
        case nil: return true;
        case cons(x0, xs0): return mem(x0, ys) && sublist(xs0, ys);
    }
}

predicate heap0(list<struct object *> unpacked) =
    [_]globals_objectListId(&globals, ?id) &*& ghost_list(id, ?objects) &*&
    foreach(objects, object_refcount) &*&
    distinct(unpacked) == true &*&
    sublist(unpacked, objects) == true &*&
    foreach(remove_all(unpacked, objects), object_inv);

predicate ref0(struct object *object, struct class *class) =
    ticket(object_ticket_base, object, ?f) &*& [f]object->class |-> class &*& [_]class->dispose |-> ?_ &*&
    [_]globals_objectListId(&globals, ?id) &*& [f]ghost_list_member_handle(id, object) &*& object != 0;

predicate ref(struct object *object) =
    ticket(object_ticket_base, object, ?f) &*& [f]object->class |-> ?class &*& [_]class->dispose |-> ?_ &*&
    [_]globals_objectListId(&globals, ?id) &*& [f]ghost_list_member_handle(id, object) &*& object != 0;

lemma void ref_not_null(void *object)
    requires ref(object);
    ensures ref(object) &*& object != 0;
{
    open ref(object);
    close ref(object);
}

@*/

void object_add_ref(void *object)
    //@ requires heap0(?unpacked) &*& ref(object);
    //@ ensures heap0(unpacked) &*& ref(object) &*& ref(object);
{
    struct object *o = object;
    //@ open heap0(_);
    //@ open ref(o);
    //@ int id = (&globals)->objectListId;
    //@ ghost_list_member_handle_lemma(id, o);
    //@ assert ghost_list(id, ?objs);
    //@ foreach_remove(o, objs);
    //@ open object_refcount(o);
    o->refCount++;
    //@ create_ticket(object_ticket_base, o);
    //@ close object_refcount(o);
    //@ foreach_unremove(o, objs);
    //@ close heap0(unpacked);
    //@ close ref(o);
    //@ close ref(o);
}

void object_release(void *object)
    //@ requires heap0(nil) &*& ref(object);
    //@ ensures heap0(nil);
{
    //@ open heap0(nil);
    //@ open ref(object);
    struct object *o = object;
    //@ int id = (&globals)->objectListId;
    //@ ghost_list_member_handle_lemma(id, o);
    //@ assert ghost_list(id, ?objs);
    //@ foreach_remove(o, objs);
    //@ open object_refcount(o);
    o->refCount--;
    //@ assert ticket(object_ticket_base, o, ?f1);
    //@ close [f1]object_ticket_base(o, _);
    //@ destroy_ticket(object_ticket_base, o);
    if (o->refCount == 0) {
        //@ foreach_remove(o, objs);
        //@ open object_inv(o);
        //@ assert ticket(object_ticket_base, o, ?f2);
        //@ close [f2]object_ticket_base(o, _);
        //@ destroy_ticket(object_ticket_base, o);
        //@ stop_counting(object_ticket_base, o);
        //@ open object_ticket_base(o, _);
        //@ ghost_list_remove(id, o);
        //@ close heap0(nil);
        dispose_func *dispose = o->class->dispose;
        //@ merge_fractions o->class->dispose |-> _;
        dispose(o);
    } else {
        //@ close object_refcount(o);
        //@ foreach_unremove(o, objs);
        //@ close heap0(nil);
    }
}

void nil_dispose(void *o)
    //@ requires true;
    //@ ensures false;
{
    abort();
}

struct class nil_class = {"nil_value", nil_dispose};

struct object nil_value = {1, &nil_class}; // One for eval_func

/*@

predicate nil_inv(void *object) = struct_object_padding(object);

predicate heap() =
    heap0(nil) &*& ref(&nil_value)
    &*& [_]class_inv(&nil_class, nil_inv)
    &*& [_]class_dispose(&nil_class, nil_dispose)
    &*& [_]class_inv(&cons_class, cons_inv)
    &*& [_]class_dispose(&cons_class, cons_dispose)
    &*& [_]class_inv(&atom_class, atom_inv)
    &*& [_]class_dispose(&atom_class, atom_dispose)
    &*& [_]class_inv(&function_class, function_inv)
    &*& [_]class_dispose(&function_class, function_dispose)
    &*& pointer(&operand_stack, ?operandStack) &*& stack(operandStack) &*& pointer(&cont_stack, ?contStack) &*& stack(contStack);

@*/

struct object *create_nil()
    //@ requires heap();
    //@ ensures heap() &*& ref(result) &*& result == &nil_value;
{
    //@ open heap();
    object_add_ref(&nil_value);
    return &nil_value;
    //@ close heap();
}

struct cons {
    struct object object;
    struct object *head;
    struct object *tail;
};

//@ predicate cons_inv(struct cons *cons) = cons->head |-> ?head &*& ref(head) &*& cons->tail |-> ?tail &*& ref(tail) &*& struct_object_padding((void *)cons) &*& malloc_block_cons(cons);

void cons_dispose(struct object *object)
    //@ requires heap0(nil) &*& object_refCount(object, _) &*& object_class(object, _) &*& cons_inv((void *)object);
    //@ ensures heap0(nil);
{
    struct cons *cons = (void *)object;
    //@ open cons_inv(cons);
    object_release(cons->head);
    object_release(cons->tail);
    free(cons);
}

struct class cons_class = {"cons", cons_dispose};

/*@

predicate cons0(struct cons *cons; struct object *head, struct object *tail) =
    object_refCount((void *)cons, 1) &*&
    object_class((void *)cons, &cons_class) &*&
    struct_object_padding((void *)cons) &*&
    cons->head |-> head &*&
    cons->tail |-> tail &*&
    malloc_block_cons(cons) &*& cons != 0;

lemma void cons0_to_cons(struct cons *cons)
    requires heap() &*& cons0(cons, ?head, ?tail) &*& ref(head) &*& ref(tail);
    ensures heap() &*& ref((void *)cons);
{
    open heap();
    open heap0(nil);
    int id = (&globals)->objectListId;
    ghost_list_add<struct object *>(id, (void *)cons);
    assert foreach(?objs, _);
    start_counting(object_ticket_base, (void *)cons);
    create_ticket(object_ticket_base, (void *)cons);
    create_ticket(object_ticket_base, (void *)cons);
    close cons_inv(cons);
    produce_function_pointer_chunk dispose_func(cons_dispose)(cons_inv)(o) { call(); }
    close object_refcount((void *)cons);
    close foreach(cons((void *)cons, objs), object_refcount);
    close object_inv((void *)cons);
    close foreach(cons((void *)cons, objs), object_inv);
    close heap0(nil);
    close heap();
    close ref((void *)cons);
}

@*/

struct cons *create_cons0(struct object *head, struct object *tail)
    //@ requires true;
    //@ ensures cons0(result, head, tail) &*& result != 0;
{
    struct cons *cons = malloc(sizeof(struct cons));
    if (cons == 0) error("create_cons: out of memory");
    (&cons->object)->refCount = 1;
    (&cons->object)->class = &cons_class;
    cons->head = head;
    cons->tail = tail;
    return cons;
}

struct cons *create_cons(struct object *head, struct object *tail)
    //@ requires heap() &*& ref(head) &*& ref(tail);
    //@ ensures heap() &*& ref((void *)result);
{
    struct cons *cons = create_cons0(head, tail);
    //@ cons0_to_cons(cons);
    return cons;
}

void destruct_cons(struct object *object, struct object **head, struct object **tail)
    //@ requires heap() &*& ref(object) &*& *head |-> _ &*& *tail |-> _;
    //@ ensures heap() &*& pointer(head, ?h) &*& ref(h) &*& pointer(tail, ?t) &*& ref(t);
{
    //@ open ref(object);
    if (object->class != &cons_class)
        error("cons expected");
    else {
        //@ open heap();
        //@ pointer_fractions_same_address(&object->class->dispose, &cons_class.dispose);
        //@ close ref0(object, &cons_class);
        //@ unpack(object);
        //@ open ref0(object, &cons_class);
        //@ open object_inv(object);
        struct cons *cons = (void *)object;
        //@ open cons_inv(cons);
        *head = cons->head;
        *tail = cons->tail;
        object_add_ref(*head);
        object_add_ref(*tail);
        //@ close cons_inv(cons);
        //@ close object_inv(object);
        //@ pack(object);
        //@ close ref(object);
        object_release(object);
        //@ close heap();
    }
}

struct atom {
    struct object object;
    struct string_buffer *chars;
};

//@ predicate atom_inv(struct atom *atom) = atom->chars |-> ?buffer &*& string_buffer(buffer, _) &*& struct_object_padding((void *)atom) &*& malloc_block_atom(atom);

void atom_dispose(struct object *object)
    //@ requires heap0(nil) &*& object_refCount(object, _) &*& object_class(object, _) &*& atom_inv((void *)object);
    //@ ensures heap0(nil);
{
    struct atom *atom = (void *)object;
    //@ open atom_inv(atom);
    string_buffer_dispose(atom->chars);
    free(atom);
}

struct class atom_class = {"atom", atom_dispose};

struct atom *create_atom(struct string_buffer *buffer)
    //@ requires heap() &*& string_buffer(buffer, _);
    //@ ensures heap() &*& ref((void *)result);
{
    struct atom *atom = malloc(sizeof(struct atom));
    if (atom == 0) abort();
    (&atom->object)->refCount = 1;
    (&atom->object)->class = &atom_class;
    atom->chars = buffer;
    return atom;
    //@ open heap();
    //@ open heap0(nil);
    //@ int id = (&globals)->objectListId;
    //@ ghost_list_add<struct object *>(id, (void *)atom);
    //@ assert foreach(?objs, _);
    //@ start_counting(object_ticket_base, (void *)atom);
    //@ create_ticket(object_ticket_base, (void *)atom);
    //@ create_ticket(object_ticket_base, (void *)atom);
    //@ close atom_inv(atom);
    //@ produce_function_pointer_chunk dispose_func(atom_dispose)(atom_inv)(o) { call(); }
    //@ close object_refcount((void *)atom);
    //@ close foreach(cons((void *)atom, objs), object_refcount);
    //@ close object_inv((void *)atom);
    //@ close foreach(cons((void *)atom, objs), object_inv);
    //@ close heap0(nil);
    //@ close heap();
    //@ close ref((void *)atom);
}

struct atom *create_atom_from_string(char *string)
    //@ requires heap() &*& [?f]string(string, ?cs);
    //@ ensures heap() &*& [f]string(string, cs) &*& ref((void *)result);
{
    struct string_buffer *buffer = create_string_buffer();
    string_buffer_append_string(buffer, string);
    return create_atom(buffer);
}

/*@

predicate cons0_stack(struct cons *parent) =
    parent == 0 ?
        emp
    :
        cons0(parent, ?head, ?tail) &*&
        (head == 0 ? emp : ref(head)) &*&
        cons0_stack((void *)tail);

@*/

struct object *parse(struct tokenizer *tokenizer)
    //@ requires heap() &*& Tokenizer(tokenizer);
    //@ ensures heap() &*& ref(result) &*& Tokenizer(tokenizer);
{
    struct cons *parent = 0;
    //@ close cons0_stack(parent);
    for (;;)
        //@ invariant cons0_stack(parent) &*& heap() &*& Tokenizer(tokenizer);
    {
        int token = tokenizer_next(tokenizer);
        if (token == 'S') {
            struct atom *atom;
            struct object *expr;
            struct string_buffer *buffer = tokenizer_get_buffer(tokenizer);
            buffer = string_buffer_copy(buffer);
            //@ tokenizer_merge_buffer(tokenizer);
            atom = create_atom(buffer);
            expr = (void *)atom;
            for (;;)
                //@ invariant cons0_stack(parent) &*& ref(expr) &*& heap() &*& Tokenizer(tokenizer);
            {
                //@ open cons0_stack(parent);
                if (parent == 0) return expr;
                if (parent->head == 0) {
                    parent->head = expr;
                    //@ ref_not_null(expr);
                    //@ close cons0_stack(parent);
                    break;
                } else {
                    struct cons *newParent = (void *)parent->tail;
                    parent->tail = expr;
                    //@ cons0_to_cons(parent);
                    expr = (void *)parent;
                    parent = newParent;
                    {
                        int newToken = tokenizer_next(tokenizer);
                        if (newToken != ')') error("Syntax error: pair: missing ')'");
                    }
                }
            }
        } else if (token == '(') {
            struct cons *cons = create_cons0(0, (void *)parent);
            parent = cons;
            //@ close cons0_stack(parent);
        } else
            error("Syntax error: expected symbol or '('");
    }
}

struct stack {
    struct object *head;
    struct stack *tail;
};

/*@

predicate stack(struct stack *stack) =
    stack == 0 ?
        emp
    :
        stack->head |-> ?head &*& ref(head) &*&
        stack->tail |-> ?tail &*& stack(tail) &*&
        malloc_block_stack(stack);

@*/

struct stack *operand_stack = 0;
struct stack *cont_stack = 0;

void stack_push(struct stack **stack, struct object *value)
    //@ requires pointer(stack, ?s) &*& stack(s) &*& ref(value);
    //@ ensures pointer(stack, ?s1) &*& stack(s1);
{
    struct stack *newStack = malloc(sizeof(struct stack));
    if (newStack == 0) abort();
    newStack->head = value;
    newStack->tail = *stack;
    *stack = newStack;
    //@ close stack(newStack);
}

struct object *stack_pop(struct stack **stack)
    //@ requires pointer(stack, ?s0) &*& stack(s0);
    //@ ensures pointer(stack, ?s1) &*& stack(s1) &*& ref(result);
{
    struct stack *s = *stack;
    if (s == 0)
        error("pop: operand stack underflow");
    else {
        //@ open stack(s0);
        struct object *result = s->head;
        *stack = s->tail;
        free(s);
        return result;
    }
}

void push(struct object *object)
    //@ requires heap() &*& ref(object);
    //@ ensures heap();
{
    //@ open heap();
    stack_push(&operand_stack, object);
    //@ close heap();
}

struct object *pop()
    //@ requires heap();
    //@ ensures heap() &*& ref(result);
{
    //@ open heap();
    return stack_pop(&operand_stack);
    //@ close heap();
}

void push_cont(struct function *function)
    //@ requires heap() &*& ref((void *)function);
    //@ ensures heap();
{
    //@ open heap();
    stack_push(&cont_stack, (void *)function);
    //@ close heap();
}

struct function *pop_cont()
    //@ requires heap();
    //@ ensures heap() &*& ref((void *)result);
{
    //@ open heap();
    struct object *result = stack_pop(&cont_stack);
    //@ close heap();
    return (void *)result;
}

typedef void apply_func(struct object *data);
    //@ requires heap() &*& ref(data);
    //@ ensures heap();

struct function {
    struct object object;
    apply_func *apply;
    struct object *data;
};

/*@

predicate function_inv(struct function *function) =
    struct_object_padding((void *)function) &*&
    function->apply |-> ?apply &*& is_apply_func(apply) == true &*&
    function->data |-> ?data &*& ref(data) &*&
    malloc_block_function(function);

@*/

void function_dispose(struct object *object)
    //@ requires heap0(nil) &*& object_refCount(object, _) &*& object_class(object, _) &*& function_inv((void *)object);
    //@ ensures heap0(nil);
{
    struct function *function = (void *)object;
    //@ open function_inv(function);
    object_release(function->data);
    free(function);
}

struct class function_class = {"function", function_dispose};

struct function *create_function(apply_func *apply, struct object *data)
    //@ requires heap() &*& is_apply_func(apply) == true &*& ref(data);
    //@ ensures heap() &*& ref((void *)result);
{
    struct function *function = malloc(sizeof(struct function));
    if (function == 0) abort();
    (&function->object)->refCount = 1;
    (&function->object)->class = &function_class;
    function->apply = apply;
    function->data = data;
    return function;
    //@ open heap();
    //@ open heap0(nil);
    //@ int id = (&globals)->objectListId;
    //@ ghost_list_add<struct object *>(id, (void *)function);
    //@ assert foreach(?objs, _);
    //@ start_counting(object_ticket_base, (void *)function);
    //@ create_ticket(object_ticket_base, (void *)function);
    //@ create_ticket(object_ticket_base, (void *)function);
    //@ close function_inv(function);
    //@ produce_function_pointer_chunk dispose_func(function_dispose)(function_inv)(o) { call(); }
    //@ close object_refcount((void *)function);
    //@ close foreach(cons((void *)function, objs), object_refcount);
    //@ close object_inv((void *)function);
    //@ close foreach(cons((void *)function, objs), object_inv);
    //@ close heap0(nil);
    //@ close heap();
    //@ close ref((void *)function);
}

/*@

lemma void unpack(void *object)
    requires heap0(?unpacked) &*& ref0(object, ?class) &*& !mem(object, unpacked);
    ensures heap0(cons(object, unpacked)) &*& ref0(object, class) &*& object_inv(object);
{
    open heap0(unpacked);
    open ref0(object, class);
    assert ghost_list(?id, ?objs);
    ghost_list_member_handle_lemma(id, object);
    mem_remove_all(object, unpacked, objs);
    foreach_remove(object, remove_all(unpacked, objs));
    close heap0(cons(object, unpacked));
    close ref0(object, class);
}

lemma void pack(void *object)
    requires heap0(cons(object, ?unpacked)) &*& object_inv(object);
    ensures heap0(unpacked);
{
    open heap0(_);
    assert ghost_list(?id, ?objs);
    mem_remove_all(object, unpacked, objs);
    foreach_unremove(object, remove_all(unpacked, objs));
    close heap0(unpacked);
}

@*/

void apply(struct object *function)
    //@ requires heap() &*& ref(function);
    //@ ensures heap();
{
    //@ open ref(function);
    if (function->class != &function_class)
        error("apply: not a function");
    {
        struct function *f = (void *)function;
        //@ struct class *fClass = function->class;
        //@ close ref0(function, _);
        //@ open heap();
        //@ pointer_fractions_same_address(&fClass->dispose, &function_class.dispose);
        //@ unpack(function);
        //@ open ref0(function, _);
        //@ open object_inv(function);
        //@ open function_inv(f);
        apply_func *applyFunc = f->apply;
        struct object *data = f->data;
        object_add_ref(data);
        //@ close function_inv(f);
        //@ close object_inv(function);
        //@ pack(function);
        //@ close ref(function);
        object_release(function);
        //@ close heap();
        applyFunc(data);
    }
}

void pop_apply(struct object *data) //@ : apply_func
    //@ requires heap() &*& ref(data);
    //@ ensures heap();
{
    struct object *f = pop();
    //@ open heap();
    object_release(data);
    //@ close heap();
    apply(f);
}

struct object *assoc(struct atom *key, struct object *map)
    //@ requires heap() &*& ref0((void *)key, &atom_class) &*& ref(map);
    //@ ensures heap() &*& ref0((void *)key, &atom_class) &*& result == 0 ? true : ref(result);
{
    for (;;)
        //@ invariant heap() &*& ref0((void *)key, &atom_class) &*& ref(map);
    {
        if (map == &nil_value) {
            //@ open heap();
            object_release(map);
            //@ close heap();
            return 0;
        }
        //@ open ref(map);
        if (map->class != &cons_class)
            error("assoc: cons cell expected");
        else {
            //@ open heap();
            //@ pointer_fractions_same_address(&map->class->dispose, &cons_class.dispose);
            //@ close ref0(map, &cons_class);
            //@ unpack(map);
            //@ open ref0(map, _);
            //@ open object_inv(map);
            struct cons *cons = (void *)map;
            //@ open cons_inv(cons);
            struct object *mapHead = cons->head;
            struct object *mapTail = cons->tail;
            object_add_ref(mapHead);
            object_add_ref(mapTail);
            //@ close cons_inv(cons);
            //@ close object_inv(map);
            //@ close ref0(map, _);
            //@ pack(map);
            //@ open ref0(map, _);
            //@ close ref(map);
            object_release(map);
            //@ open ref(mapHead);
            if (mapHead->class != &cons_class)
                error("assoc: cons cell expected at head");
            else {
                struct cons *entry = (void *)mapHead;
                //@ pointer_fractions_same_address(&mapHead->class->dispose, &cons_class.dispose);
                //@ close ref0(mapHead, &cons_class);
                //@ unpack(mapHead);
                //@ open ref0(mapHead, _);
                //@ open object_inv(mapHead);
                //@ open cons_inv(entry);
                struct object *entryHead = entry->head;
                struct object *entryTail = entry->tail;
                object_add_ref(entryHead);
                object_add_ref(entryTail);
                //@ close cons_inv(entry);
                //@ close object_inv(mapHead);
                //@ close ref0(mapHead, _);
                //@ pack(mapHead);
                //@ open ref0(mapHead, _);
                //@ close ref(mapHead);
                object_release(mapHead);
                if (entryHead == (void *)key) {
                    object_release(entryHead);
                    object_release(mapTail);
                    //@ close heap();
                    //@ ref_not_null(entryTail);
                    return entryTail;
                }
                //@ open ref(entryHead);
                if (entryHead->class != &atom_class)
                    error("assoc: atom expected at head of head");
                else {
                    //@ pointer_fractions_same_address(&entryHead->class->dispose, &atom_class.dispose);
                    //@ close ref0(entryHead, &atom_class);
                    //@ unpack(entryHead);
                    //@ open ref0(entryHead, _);
                    //@ open object_inv(entryHead);
                    struct atom *key0 = (void *)entryHead;
                    //@ open atom_inv(key0);
                    
                    //@ unpack((void *)key);
                    //@ open ref0((void *)key, _);
                    //@ open object_inv((void *)key);
                    //@ open atom_inv(key);
                    
                    bool eq = string_buffer_equals(key->chars, key0->chars);
                    
                    //@ close atom_inv(key);
                    //@ close object_inv((void *)key);
                    //@ pack((void *)key);
                    //@ close ref0((void *)key, _);
                    
                    //@ close atom_inv(key0);
                    //@ close object_inv(entryHead);
                    //@ pack(entryHead);
                    //@ close ref(entryHead);
                    
                    object_release(entryHead);
                    
                    if (eq) {
                        object_release(mapTail);
                        //@ close heap();
                        //@ ref_not_null(entryTail);
                        return entryTail;
                    }
                    object_release(entryTail);
                    //@ close heap();
                    map = mapTail;
                }
            }
        }
    }
}

struct object *map_cons(struct atom *key, struct object *value, struct object *map)
    //@ requires heap() &*& ref((void *)key) &*& ref(value) &*& ref(map);
    //@ ensures heap() &*& ref(result);
{
    struct cons *entry = create_cons((void *)key, value);
    struct cons *cons = create_cons((void *)entry, map);
    return (void *)cons;
}

struct object *map_cons_s(char *key, struct object *value, struct object *map)
    //@ requires heap() &*& [?f]string(key, ?cs) &*& ref(value) &*& ref(map);
    //@ ensures heap() &*& [f]string(key, cs) &*& ref(result);
{
    struct atom *atom = create_atom_from_string(key);
    return map_cons(atom, value, map);
}

struct object *map_cons_s_func_nil(char *key, apply_func *function, struct object *map)
    //@ requires heap() &*& [?f]string(key, ?cs) &*& is_apply_func(function) == true &*& ref(map);
    //@ ensures heap() &*& [f]string(key, cs) &*& ref(result);
{
    struct object *data = create_nil();
    void *func = create_function(function, data);
    return map_cons_s(key, func, map);
}

void eval(struct object *data) //@ : apply_func
    //@ requires heap() &*& ref(data);
    //@ ensures heap();
{
    struct object *envs;
    struct object *forms;
    struct object *env;
    struct object *expr;
    destruct_cons(data, &envs, &expr);
    //@ open heap();
    object_add_ref(envs);
    //@ close heap();
    destruct_cons(envs, &forms, &env);
    //@ open ref(expr);
    if (expr->class == &atom_class) {
        struct object *value;
        //@ open heap();
        //@ pointer_fractions_same_address(&expr->class->dispose, &atom_class.dispose);
        object_add_ref(env);
        //@ close heap();
        //@ close ref0(expr, _);
        value = assoc((void *)expr, env);
        if (value == 0) error("eval: no such binding");
        //@ open heap();
        object_release(envs);
        object_release(forms);
        object_release(env);
        //@ open ref0(expr, _);
        //@ close ref(expr);
        object_release(expr);
        //@ close heap();
        push(value);
    } else if (expr->class == &cons_class) {
        struct object *f_expr;
        struct object *arg_expr;
        struct object *form;
        bool isForm;
        
        //@ close ref(expr);
        destruct_cons(expr, &f_expr, &arg_expr);
        
        //@ open ref(f_expr);
        isForm = f_expr->class == &atom_class;
        if (isForm) {
            //@ open heap();
            //@ pointer_fractions_same_address(&f_expr->class->dispose, &atom_class.dispose);
            object_add_ref(forms);
            //@ close heap();
            //@ close ref0(f_expr, _);
            form = assoc((void *)f_expr, forms);
            //@ open ref0(f_expr, _);
            isForm = form != 0;
        }
        //@ close ref(f_expr);
        //@ open heap();
        object_release(forms);
        object_release(env);
        if (isForm) {
            void *value;
            object_release(f_expr);
            //@ close heap();
            value = create_cons((void *)envs, arg_expr);
            push(value);
            apply((void *)form);
        } else {
            void *functionData;
            void *function;
            
            //@ close heap();
            
            functionData = create_nil();
            function = create_function(pop_apply, functionData);
            push_cont(function);
            
            //@ open heap();
            object_add_ref(envs);
            //@ close heap();
            functionData = create_cons(envs, f_expr);
            function = create_function(eval, functionData);
            push_cont(function);
            
            functionData = create_cons(envs, arg_expr);
            function = create_function(eval, functionData);
            push_cont(function);
        }
    } else
        error("Cannot evaluate: not an atom or a cons.");
}

void print_atom(struct object *data) //@ : apply_func
    //@ requires heap() &*& ref(data);
    //@ ensures heap();
{
    struct object *arg = pop();
    //@ open ref(arg);
    if (arg->class != &atom_class) error("print_atom: argument is not an atom");
    //@ open heap();
    //@ pointer_fractions_same_address(&arg->class->dispose, &atom_class.dispose);
    //@ close ref0(arg, _);
    //@ unpack(arg);
    //@ open ref0(arg, _);
    //@ open object_inv(arg);
    //@ open atom_inv((void *)arg);
    print_string_buffer(((struct atom *)(void *)arg)->chars);
    //@ close atom_inv((void *)arg);
    //@ close object_inv(arg);
    //@ pack(arg);
    //@ close ref(arg);
    object_release(data);
    object_release(arg);
    //@ close heap();
    push(create_nil());
}

void quote_function(struct object *data) //@ : apply_func
    //@ requires heap() &*& ref(data);
    //@ ensures heap();
{
    struct object *arg = pop();
    struct object *envs;
    struct object *body;
    destruct_cons(arg, &envs, &body);
    
    //@ open heap();
    object_release(envs);
    object_release(data);
    //@ close heap();
    push(body);
}

void fun_apply_function(struct object *data) //@ : apply_func
    //@ requires heap() &*& ref(data);
    //@ ensures heap();
{
    struct object *arg = pop();
    
    struct object *envs;
    struct object *forms;
    struct object *env;
    struct object *expr;
    struct object *param;
    struct object *body;
    
    destruct_cons(data, &envs, &expr);
    destruct_cons(envs, &forms, &env);
    destruct_cons(expr, &param, &body);
    
    //@ open ref(param);
    if (param->class != &atom_class)
        error("fun: param should be an atom");
    else {
        //@ close ref(param);
        struct object *newEnv = map_cons((void *)param, arg, env);

        void *newEnvs = create_cons(forms, newEnv);
        void *newData = create_cons(newEnvs, body);
        void *newFunction = create_function(eval, newData);
        push_cont(newFunction);
    }
}

void fun_function(struct object *data) //@ : apply_func
    //@ requires heap() &*& ref(data);
    //@ ensures heap();
{
    struct object *arg = pop();
    void *newFunction;
    //@ open heap();
    object_release(data);
    //@ close heap();
    newFunction = create_function(fun_apply_function, arg);
    push(newFunction);
}

/*@

predicate hide_object_refCount(struct object *object, int refCount) = object->refCount |-> refCount;

lemma void object_not_null(struct object *object)
    requires object->refCount |-> ?r;
    ensures object->refCount |-> r &*& object != 0;
{
    close [1/2]hide_object_refCount(object, _);
    open object_refCount(object, _);
    integer_to_chars((void *)object);
    if (object == 0) {
        chars_zero();
    }
    close [1/2]object_refCount(object, _);
    open [1/2]hide_object_refCount(object, _);
}

lemma void init_heap()
    requires module(rcl, true);
    ensures heap();
{
    open_module();
    
    object_not_null(&nil_value);
    
    int objectListId = create_ghost_list();
    (&globals)->objectListId = objectListId;
    leak globals_objectListId(&globals, _);
    
    close foreach(nil, object_refcount);
    close foreach(nil, object_inv);
    
    (&nil_class)->inv = nil_inv;
    leak class_dispose(&nil_class, _) &*& class_inv(&nil_class, _) &*& class_name(&nil_class, _);
    
    (&cons_class)->inv = cons_inv;
    leak class_dispose(&cons_class, _) &*& class_inv(&cons_class, _) &*& class_name(&cons_class, _);
    
    (&atom_class)->inv = atom_inv;
    leak class_dispose(&atom_class, _) &*& class_inv(&atom_class, _) &*& class_name(&atom_class, _);
    
    (&function_class)->inv = function_inv;
    leak class_dispose(&function_class, _) &*& class_inv(&function_class, _) &*& class_name(&function_class, _);
    
    ghost_list_add(objectListId, &nil_value);
    close object_ticket_base(&nil_value, &nil_class);
    start_counting(object_ticket_base, &nil_value);
    create_ticket(object_ticket_base, &nil_value);
    create_ticket(object_ticket_base, &nil_value);
    close object_refcount(&nil_value);
    close foreach(cons(&nil_value, nil), object_refcount);
    close nil_inv(&nil_value);
    produce_function_pointer_chunk dispose_func(nil_dispose)(nil_inv)(o) { call(); }
    close object_inv(&nil_value);
    close foreach(cons(&nil_value, nil), object_inv);
    
    close heap0(nil);
    
    close ref(&nil_value);
    
    close stack(0);
    close stack(0);
    
    close heap();
    
    leak globals_dummy(&globals, _);
}

@*/

int my_getchar() //@ : charreader
    //@ requires true;
    //@ ensures true;
{
    return getchar();
}

int main() //@ : main_full(rcl)
    //@ requires module(rcl, true);
    //@ ensures true;
{
    //@ init_heap();
    
    struct object *forms;
    struct object *env;
    struct tokenizer *tokenizer;
    
    forms = create_nil();
    forms = map_cons_s_func_nil("quote", quote_function, forms);
    forms = map_cons_s_func_nil("fun", fun_function, forms);
    
    env = create_nil();
    env = map_cons_s_func_nil("print_atom", print_atom, env);
    
    tokenizer = tokenizer_create(my_getchar);
    
    for (;;)
        //@ invariant heap() &*& ref(forms) &*& ref(env) &*& Tokenizer(tokenizer);
    {
        struct object *expr = parse(tokenizer);
        void *object;
        
        //@ open heap();
        object_add_ref(forms);
        object_add_ref(env);
        //@ close heap();
        object = create_cons(forms, env);
        object = create_cons(object, expr);
        object = create_function(eval, object);
        push_cont(object);
        for (;;)
            //@ invariant heap();
        {
            //@ open heap();
            if (cont_stack == 0) break;
            //@ close heap();
            object = pop_cont();
            apply(object);
        }
        //@ close heap();
        object = pop();
        //@ open heap();
        object_release(object);
        //@ close heap();
    }
}