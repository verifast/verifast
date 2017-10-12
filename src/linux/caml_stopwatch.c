#define _GNU_SOURCE
#include <sched.h>
#include <x86intrin.h>
#include <caml/mlvalues.h>
#include <caml/alloc.h>
#include <unistd.h>

value caml_stopwatch_getpid() {
    return copy_int32(getpid());
}

value caml_lock_process_to_processor_1() {
#ifdef __linux__ // MacOS does not support thread affinity; see http://developer.apple.com/library/mac/#releasenotes/Performance/RN-AffinityAPI/
    cpu_set_t mask;
    CPU_ZERO(&mask);
    CPU_SET(0, &mask);
    pid_t pid = 0;
    sched_setaffinity(pid, sizeof(cpu_set_t), &mask);
#endif
    return Val_unit;
}

value caml_stopwatch_processor_ticks() {
    return copy_int64(__rdtsc());
}

struct stopwatch {
    unsigned long long counter;
    unsigned long long startTimestamp;
};

#define NO_TIMESTAMP (0x0100000000000000LLU)

value caml_stopwatch_create() {
    struct stopwatch *block = (void *)caml_alloc_small(4, Abstract_tag);
    block->counter = 0;
    block->startTimestamp = NO_TIMESTAMP;
    return (value)block;
}

value caml_stopwatch_start(value stopwatch) {
    struct stopwatch *s = (void *)stopwatch;
    s->startTimestamp = __rdtsc();
    return Val_unit;
}

value caml_stopwatch_stop(value stopwatch) {
    struct stopwatch *s = (void *)stopwatch;
    unsigned long long tsc = __rdtsc();
    s->counter += tsc - s->startTimestamp;
    s->startTimestamp = NO_TIMESTAMP;
    return Val_unit;
}

value caml_stopwatch_ticks(value stopwatch) {
    struct stopwatch *s = (void *)stopwatch;
    return copy_int64(s->counter);
}
