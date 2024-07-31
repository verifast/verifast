#include <stdint.h>

struct point {
  int x;
  int y;
};

union u {
  short x;
  int y;
};

uint32_t read_and_inc_uint32(uint32_t *p)
//@ requires *p |-> ?value &*& value < 2000000000;
//@ ensures *p |-> value + 1 &*& result == value;
{
    return (*p)++;
}

/*@

lemma void has_type_field_ptr_test(struct point *p)
    requires has_type(p, &typeid(struct point)) == true;
    ensures has_type(&p->y, &typeid(int)) == true;
{}

lemma void has_type_union_variant_test(union u *p)
    requires has_type(p, &typeid(union u)) == true;
    ensures has_type(&p->y, &typeid(int)) == true;
{}

lemma int *effective_types(void *p)
    requires chars(p, sizeof(int), _);
    ensures *result |-> _;
{
    chars_to_integer(p); //~
}

@*/
