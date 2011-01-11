#ifdef WIN32
#include <windows.h>
#else
#include <pthread.h>
#endif
#include <stdlib.h> /* abort */

#include "threading.h"

#ifdef WIN32
struct thread {
    HANDLE handle;
};

// The callback function needs to respect a non-standard calling convention.
struct run_closure {
    void (*run)(void *data);
    void *data;
};

DWORD WINAPI run_closure_run(LPVOID argument)
{
    struct run_closure *closure = (struct run_closure *)argument;
    void (*run)(void *data) = closure->run;
    void *data = closure->data;
    free(closure);
    run(data);
    return 0;
}
#else
struct thread {
    pthread_t id;
};
#endif

struct thread *thread_start_joinable(void* run, void *data)
{
#ifdef WIN32
    struct run_closure *closure;
    HANDLE result;
    struct thread *t;
    
    closure = malloc(sizeof(struct run_closure));
    closure->run = run;
    closure->data = data;
    result = CreateThread(0, 0, run_closure_run, closure, 0, 0);
    if (result == NULL)
        abort();
    t = malloc(sizeof(struct thread));
    if (t == 0) abort();
    t->handle = result;
    return t;
#else
    pthread_t id;
    
    int result = pthread_create(&id, 0, (void *(*)(void *))run, data);
    if (result != 0)
        abort();
    struct thread *t = malloc(sizeof(struct thread));
    if (t == 0) abort();
    t->id = id;
    return t;
#endif
}

void thread_join(struct thread *t)
{
#ifdef WIN32
    DWORD result = WaitForSingleObject(t->handle, INFINITE);
    if (result != WAIT_OBJECT_0) abort();
    CloseHandle(t->handle);
#else
    int result = pthread_join(t->id, 0);
    if (result != 0) abort();
#endif
    free(t);
}

void thread_dispose(struct thread* t)
{
#ifdef WIN32
    CloseHandle(t->handle);
#else
    pthread_detach(t->id);
#endif
    free(t);
}

void thread_start(void* run, void *data)
{
    struct thread *t = thread_start_joinable(run, data);
    thread_dispose(t);
}

struct lock {
#ifdef WIN32
    CRITICAL_SECTION criticalSection;
#else
    pthread_mutex_t mutex;
#endif
};

struct lock *create_lock()
{
    struct lock *lock = malloc(sizeof(struct lock));
#ifdef WIN32
    InitializeCriticalSection(&(lock->criticalSection));
#else
    int result = pthread_mutex_init(&(lock->mutex), 0);
    if (result != 0)
        abort();
#endif
    return lock;
}

void lock_acquire(struct lock *lock)
{
#ifdef WIN32
    EnterCriticalSection(&(lock->criticalSection));
#else
    pthread_mutex_lock(&(lock->mutex));
#endif
}

void lock_release(struct lock *lock)
{
#ifdef WIN32
    LeaveCriticalSection(&(lock->criticalSection));
#else
    pthread_mutex_unlock(&(lock->mutex));
#endif
}

void lock_dispose(struct lock *lock)
{
#ifdef WIN32
    DeleteCriticalSection(&(lock->criticalSection));
#else
    pthread_mutex_destroy(&(lock->mutex));
#endif
    free(lock);
}

struct mutex {
#ifdef WIN32
    CRITICAL_SECTION criticalSection;
    DWORD ownerThreadId;
#else
    pthread_mutex_t mutex;
    pthread_t ownerThreadId;
#endif
};

struct mutex *create_mutex()
{
    struct mutex *mutex = malloc(sizeof(struct mutex));
#ifdef WIN32
    InitializeCriticalSection(&(mutex->criticalSection));
#else
    int result = pthread_mutex_init(&(mutex->mutex), 0);
    if (result != 0)
        abort();
#endif
    mutex->ownerThreadId = 0;
    return mutex;
}

void mutex_acquire(struct mutex *mutex)
{
#ifdef WIN32
    EnterCriticalSection(&(mutex->criticalSection));
#else
    pthread_mutex_lock(&(mutex->mutex));
#endif
    if (mutex->ownerThreadId != 0)
        abort();
#ifdef WIN32
    mutex->ownerThreadId = GetCurrentThreadId();
#else
    mutex->ownerThreadId = pthread_self();
#endif
}

void mutex_release(struct mutex *mutex)
{
#ifdef WIN32
    if (mutex->ownerThreadId != GetCurrentThreadId())
        abort();
    mutex->ownerThreadId = 0;
    LeaveCriticalSection(&(mutex->criticalSection));
#else
    if (!pthread_equal(mutex->ownerThreadId, pthread_self()))
        abort();
    mutex->ownerThreadId = 0;
    pthread_mutex_unlock(&(mutex->mutex));
#endif
}

void mutex_dispose(struct mutex *mutex)
{
#ifdef WIN32
    DeleteCriticalSection(&(mutex->criticalSection));
#else
    pthread_mutex_destroy(&(mutex->mutex));
#endif
    free(mutex);
}