#include "ticketlock.h"

ticketlock lock;
unsigned long long flag;

void acquirer()
{
  ticketlock_acquire(lock);
  atomic_store_counter(&flag, 1);
}

int main()
{
  lock = create_ticketlock();
  fork(acquirer);

  for (;;)
  {
    unsigned long long value;
    value = atomic_load_counter(&flag);
    if (value == 1)
      break;
  }
  ticketlock_release(lock);
  return 0;
}
