#include <windows.h>
#include <caml/fail.h>
#include <caml/mlvalues.h>
#include <caml/alloc.h>

value caml_query_performance_frequency() {
    LARGE_INTEGER freq;
    if (!QueryPerformanceFrequency(&freq)) {
        caml_failwith("QueryPerformanceFrequency");
        return 0;
    }
    return caml_copy_int64(freq.QuadPart);
}

value caml_query_performance_counter() {
    LARGE_INTEGER count;
    if (!QueryPerformanceCounter(&count)) {
        caml_failwith("QueryPerformanceCounter");
        return 0;
    }
    return caml_copy_int64(count.QuadPart);
}