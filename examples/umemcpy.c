#include <string.h>

void umemcpy(unsigned char *dest, unsigned char *src, unsigned count)
    //@ requires uchars_(dest, count, _) &*& [?f]uchars(src, count, ?cs);
    //@ ensures uchars(dest, count, cs) &*& [f]uchars(src, count, cs);
{
    memcpy(dest, src, count);
}
