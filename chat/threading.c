#include <pthread.h>
#include <stdlib.h> /* abort */

#include "threading.h"

void thread_start(void run(void *data), void *data)
{
    pthread_t id;
    
    int result = pthread_create(&id, 0, (void *(*)(void *))run, data);
    if (result != 0)
        abort();
}

struct lock {
    pthread_mutex_t mutex;
};

struct lock *create_lock()
{
    struct lock *lock = malloc(sizeof(struct lock));
    int result = pthread_mutex_init(&(lock->mutex), 0);
    if (result != 0)
        abort();
    return lock;
}

void lock_acquire(struct lock *lock)
{
    pthread_mutex_lock(&(lock->mutex));
}

void lock_release(struct lock *lock)
{
    pthread_mutex_unlock(&(lock->mutex));
}
