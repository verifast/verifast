#include <windows.h>
#include <intrin.h>
#include <caml/mlvalues.h>
#include <caml/alloc.h>

value caml_stopwatch_getpid() {
    return copy_int32(GetCurrentProcessId());
}

value caml_lock_process_to_processor_1() {
    HANDLE currentProcess = GetCurrentProcess();
    SetProcessAffinityMask(currentProcess, 1);
    return Val_unit;
}

value caml_stopwatch_processor_ticks() {
    return copy_int64(__rdtsc());
}

struct stopwatch {
    unsigned __int64 counter;
    unsigned __int64 startTimestamp;
};

#define NO_TIMESTAMP (0x0100000000000000i64)

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
    unsigned __int64 tsc = __rdtsc();
    s->counter += tsc - s->startTimestamp;
    s->startTimestamp = NO_TIMESTAMP;
    return Val_unit;
}

value caml_stopwatch_ticks(value stopwatch) {
    struct stopwatch *s = (void *)stopwatch;
    return copy_int64(s->counter);
}