#include "libraries.h"
#include "windows.h"

struct library *load_library(char *name)
{
    // int wideCharCount;
    struct library *result;
    // MultiByteToWideChar(CP_UTF8, 0, name, -1, 0, &wideCharCount);
    result = (void *)LoadLibrary(name);
    if (result == 0) {
        DWORD error = GetLastError();
        abort();
    }
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
}