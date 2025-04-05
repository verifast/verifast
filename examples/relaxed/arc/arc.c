void fetch_and_increment_relaxed(unsigned long long *p);
unsigned long long fetch_and_decrement_release(unsigned long long *p);
void fence_acquire();

struct arc {
  unsigned long long counter;
  int payload;
};

typedef struct arc *arc;

arc create_arc(int payload)
{
  arc result = malloc(sizeof(struct arc));
  if (result == 0) abort();
  arc->counter = 1;
  arc->payload = payload;
  return arc;
}

int arc_get_payload(arc arc)
{
  return arc->payload;
}

void arc_clone(arc arc)
{
  fetch_and_increment_relaxed(&arc->counter);
}

void arc_drop(arc arc)
{
  unsigned long long counter0 = fetch_and_decrement_release(&arc->counter);
  if (counter0 == 1) {
    fence_acquire();
    free(arc);
  }
}
