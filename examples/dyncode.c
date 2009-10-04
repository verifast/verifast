#include "bool.h"
#include "assert.h"
#include "malloc.h"
#include "stdlib.h"

typedef int sillyfunc/*@(predicate() p)@*/();
    //@ requires [?f]p();
    //@ ensures [f]p() &*& result == 1;

//@ predicate_ctor chars_ctor(char *start, chars contents)() = chars(start, contents);

int main() //@ : main
    //@ requires true;
    //@ ensures true;
{
    char *code = malloc(4);
    if (code == 0) abort();
    sillyfunc *funcptr = 0;
    int funcresult = 0;
    
    // x86 machine code:
    // 33 C0   xor eax, eax
    // 40      inc eax
    // C3      ret
    
    //@ open chars(code, _);
    *(code + 0) = 0x33;
    //@ open chars(code + 1, _);
    *(code + 1) = (char)0xC0;
    //@ open chars(code + 2, _);
    *(code + 2) = 0x40;
    //@ open chars(code + 3, _);
    *(code + 3) = (char)0xC3;
    //@ assert chars(code + 4, ?cs);
    //@ close chars(code + 3, chars_cons((char)0xC3, cs));
    //@ close chars(code + 2, chars_cons(0x40, chars_cons((char)0xC3, cs)));
    //@ close chars(code + 1, chars_cons((char)0xC0, chars_cons(0x40, chars_cons((char)0xC3, cs))));
    //@ close chars(code, chars_cons(0x33, chars_cons((char)0xC0, chars_cons(0x40, chars_cons((char)0xC3, cs)))));
    
    //@ assert chars(code, ?contents);
    //@ close chars_ctor(code, contents)();
    funcptr = (void *)code;
    {
        /*@
        lemma void helper()
            requires true;
            ensures [_]is_sillyfunc(funcptr, chars_ctor(code, contents));
        {
            assume(false);
        }
        @*/
        //@ helper();
    }
    funcresult = funcptr();
    //@ open chars_ctor(code, contents)();
    free(code);
    
    assert(funcresult == 1);
    
    return 0;
}