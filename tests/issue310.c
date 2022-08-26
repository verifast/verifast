typedef struct s {
  int data;
} s_data;

void foo(s_data **ps)
//@ requires *ps |-> ?s &*& s->data |-> ?d &*& 0 <= d;
//@ ensures *ps |-> s &*& s->data |-> d - 1;
{
  s_data **e;
  e = ps;
  s_data **f = e;
  (*f)->data -= 1;
}
