#include "libraries.h"
#include "windows.h"

// Keeps track of loaded libraries to ensure that the same library is never loaded twice.


CRITICAL_SECTION *loaderLock;
struct loaded_lib {
    struct loaded_lib *next;
    void *handle;
};
struct loaded_lib *loadedLibs;

struct library *load_library(char *name)
{
    // int wideCharCount;
    struct library *result;
    CRITICAL_SECTION *lock;
    // MultiByteToWideChar(CP_UTF8, 0, name, -1, 0, &wideCharCount);
    result = (void *)LoadLibrary(name);
    if (result == 0) {
        DWORD error = GetLastError();
        abort();
    }
    lock = (CRITICAL_SECTION * volatile)loaderLock;
    if (lock == 0) {
        CRITICAL_SECTION *cs = malloc(sizeof(CRITICAL_SECTION));
        void *original;
        if (cs == 0) abort();
        InitializeCriticalSection(cs);
        original = InterlockedCompareExchangePointer(&loaderLock, cs, 0);
        if (original != 0) {
            DeleteCriticalSection(cs);
            free(cs);
            lock = original;
        } else
            lock = cs;
    }
    EnterCriticalSection(lock);
    {
        struct loaded_lib *l;
        for (l = loadedLibs; l != 0; l = l->next) {
            if (l->handle == result) {
                FreeLibrary((void *)result);
                return 0;
            }
        }
        l = malloc(sizeof(struct loaded_lib));
        if (l == 0) abort();
        l->next = loadedLibs;
        l->handle = result;
        loadedLibs = l;
    }
    LeaveCriticalSection(lock);
    return result;
}

void *library_lookup_symbol(struct library *library, char *symbol)
{
    void *result = GetProcAddress((void *)library, symbol);
    if (result == 0) abort();
    return result;
}

void library_free(struct library *library)
{
    FreeLibrary((void *)library);
    EnterCriticalSection(loaderLock);
    {
        struct loaded_lib **pl = &loadedLibs;
        while ((*pl)->handle != library) pl = &(*pl)->next;
        *pl = (*pl)->next;
    }
    LeaveCriticalSection(loaderLock);
}