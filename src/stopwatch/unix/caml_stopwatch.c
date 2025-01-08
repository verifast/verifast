#define _GNU_SOURCE
#include <sched.h>
#if __aarch64__
    #include <time.h>
#else
    #include <x86intrin.h>
#endif
#include <caml/mlvalues.h>
#include <caml/alloc.h>
#include <unistd.h>

value caml_stopwatch_getpid() {
    return caml_copy_int32(getpid());
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

static unsigned long long get_processor_ticks() {
#if __aarch64__
    return clock_gettime_nsec_np(CLOCK_UPTIME_RAW);
#else
    return __rdtsc();
#endif
}

value caml_stopwatch_processor_ticks() {
    return caml_copy_int64(get_processor_ticks());
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
    s->startTimestamp = get_processor_ticks();
    return Val_unit;
}

value caml_stopwatch_stop(value stopwatch) {
    struct stopwatch *s = (void *)stopwatch;
    unsigned long long tsc = get_processor_ticks();
    s->counter += tsc - s->startTimestamp;
    s->startTimestamp = NO_TIMESTAMP;
    return Val_unit;
}

value caml_stopwatch_ticks(value stopwatch) {
    struct stopwatch *s = (void *)stopwatch;
    return caml_copy_int64(s->counter);
}