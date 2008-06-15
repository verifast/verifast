struct node {
  struct node *next;
  int value;
};

struct list {
  struct node *first;
  struct node *last;
};

struct list *create_list() {
  struct list *l = malloc(sizeof(struct list));
  struct node *n = malloc(sizeof(struct node));
  l->first = n;
  l->last = n;
  return l;
}

void add(struct list *list, int x) {
  struct node *n = malloc(sizeof(struct node));
  struct node *l = list->last;
  l->next = n;
  l->value = x;
  list->last = n;
}

void append(struct list *list1, struct list *list2) {
  struct list *l = list1->last;
  l->next = list2->first->next;
  l->value = list2->first->value;
  list1->last = list2->last;
}

int length(struct list *list) {
  struct node *n = list->first;
  int c = 0;
  while (n != list->last) {
    n = n->next;
    c = c + 1;
  }
  return c;
}

int lookup(struct list *list, int index) {
  struct node *n = list->first;
  while (0 < index) {
    n = n->next;
    index = index - 1;
  }
  return n->value;
}

void main() {
  struct list *l1 = create_list();
  struct list *l2 = create_list();
  add(l1, 10);
  add(l1, 20);
  add(l1, 30);
  add(l2, 40);
  add(l2, 50);
  add(l2, 60);
  append(l1, l2);
  assert(length(l1) == 6);
  assert(lookup(l1, 0) == 10);
  assert(lookup(l1, 1) == 20);
  assert(lookup(l1, 2) == 30);
  assert(lookup(l1, 3) == 40);
  assert(lookup(l1, 4) == 50);
  assert(lookup(l1, 5) == 60);
}
