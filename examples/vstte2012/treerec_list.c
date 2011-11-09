#include "stdlib.h"
#include "treerec_list.h"

struct node {
    struct node *next;
    int value;
};

/*@

predicate nodes(struct node *n; list<int> values) =
    n == 0 ?
        values == nil
    :
        n->next |-> ?next &*& n->value |-> ?value &*& malloc_block_node(n) &*&
        nodes(next, ?values0) &*&
        values == cons(value, values0);

@*/

struct list {
    struct node *head;
};

/*@

predicate list(struct list *l; list<int> values) =
    l->head |-> ?head &*& malloc_block_list(l) &*& nodes(head, values);

@*/

struct list *create_list()
    //@ requires true;
    //@ ensures list(result, nil);
{
    struct list *list = malloc(sizeof(struct list));
    if (list == 0) { abort(); }
    list->head = 0;
    return list;
}

void list_push(struct list *list, int value)
    //@ requires list(list, ?values);
    //@ ensures list(list, cons(value, values));
{
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) { abort(); }
    n->next = list->head;
    n->value = value;
    list->head = n;
}

bool list_is_empty(struct list *list)
    //@ requires list(list, ?values);
    //@ ensures list(list, values) &*& result == (values == nil);
{
    //@ { struct node *head = list->head; open nodes(head, _); }
    return list->head == 0;
}

int list_head(struct list *list)
    //@ requires list(list, ?values) &*& values != nil;
    //@ ensures list(list, values) &*& result == head(values);
{
    //@ { struct node *head = list->head; open nodes(head, _); }
    return list->head->value;
}

int list_pop(struct list *list)
    //@ requires list(list, ?values) &*& values != nil;
    //@ ensures list(list, tail(values)) &*& result == head(values);
{
    struct node *head = list->head;
    //@ open nodes(head, _);
    int result = head->value;
    list->head = head->next;
    free(head);
    return result;
}

void list_dispose(struct list *list)
    //@ requires list(list, ?values);
    //@ ensures true;
{
    struct node *n = list->head;
    while (n != 0)
        //@ invariant nodes(n, _);
    {
        struct node *next = n->next;
        free(n);
        n = next;
    }
    free(list);
}

int main()
    //@ requires true;
    //@ ensures true;
{
    struct list *s = create_list();
    list_push(s, 10);
    list_push(s, 20);
    int x = list_pop(s);
    assert(x == 20);
    int y = list_pop(s);
    assert(y == 10);
    list_dispose(s);
    return 0;
}