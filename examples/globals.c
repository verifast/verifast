static int x;

struct counter {
  int f;
};

static struct counter* c;

void m()
  //@ requires integer(&x, 7) &*& pointer(&c, ?ctr) &*& counter_f(ctr, ?v);
  //@ ensures integer(&x, 8) &*& pointer(&c, ctr) &*& counter_f(ctr, v + 1);
{
  int y = x;
  x = y + 1;
  c->f = c->f + 1;
}

