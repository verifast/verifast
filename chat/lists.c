#include <malloc.h>
#include "bool.h"
#include "lists.h"

struct node {
    void *value;
    struct node *next;
};

struct list {
    struct node *head;
};

struct list *create_list()
{
    struct list *list = malloc(sizeof(list));
    list->head = 0;
    return list;
}

struct iter {
    struct node *next;
};

struct iter *list_create_iter(struct list *list)
{
    struct iter *iter = malloc(sizeof(struct iter));
    iter->next = list->head;
    return iter;
}

bool iter_has_next(struct iter *iter)
{
    return iter->next != 0;
}

void *iter_next(struct iter *iter)
{
    struct node *node = iter->next;
    iter->next = node->next;
    return node->value;
}

void iter_dispose(struct iter *iter)
{
    free(iter);
}

void list_add(struct list *list, void *element)
{
    struct node *node = malloc(sizeof(struct node));
    node->value = element;
    node->next = list->head;
    list->head = node;
}

void list_remove(struct list *list, void *element)
{
    struct node **next = &(list->head);
    while ((*next)->value != element)
        *next = (*next)->next;
    *next = (*next)->next;
}
