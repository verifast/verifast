void thread_start(void run(void *data), void *data);

struct lock;

struct lock *create_lock();
void lock_acquire(struct lock *lock);
void lock_release(struct lock *lock);
