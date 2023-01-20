struct point {
  int x;
  int y;
};

union u {
  short x;
  int y;
};

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
