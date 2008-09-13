struct list;
struct iter;

struct list *create_list();
struct iter *list_create_iter(struct list *list);
bool iter_has_next(struct iter *iter);
void *iter_next(struct iter *iter);
void iter_dispose(struct iter *iter);
void list_add(struct list *list, void *element);
void list_remove(struct list *list, void *element);
