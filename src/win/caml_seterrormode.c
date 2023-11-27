#include <windows.h>
#include <caml/mlvalues.h>

value caml_SetErrorMode()
{
        SetErrorMode(SEM_FAILCRITICALERRORS);
        return Val_unit;
}
