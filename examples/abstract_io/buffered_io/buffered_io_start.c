#include "stdio_write.h"
#include "buffered_io.h"

//@ import_module stdio;

/*@

lemma void lift_beep_()
    nonghost_callers_only
    requires stdout_buffer(nil) &*& token(?P0) &*& beep_(P0, ?P1);
    ensures token(?P0_) &*& beep_(P0_, unspec_stdout_buffer_token(P1));
{
    {
        predicate Frame() = stdout_buffer(nil);
        predicate P0_() = P0() &*& stdout_buffer(nil);
        produce_lemma_function_pointer_chunk implies(P0_, True, P0, Frame)() { open P0_(); close Frame(); };
        produce_lemma_function_pointer_chunk implies(P1, Frame, unspec_stdout_buffer_token(P1), True)() {
            open Frame();
            implies_refl(P1, True);
            close write_chars_(P1, nil, P1);
            close token(P1);
            close stdout_buffer_token(nil, P1);
            close unspec_stdout_buffer_token(P1)();
        };
        close conseq(P0_, P0, P1, unspec_stdout_buffer_token(P1));
        beep__weaken(P0_, P0, P1, unspec_stdout_buffer_token(P1));
        open token(P0);
        close P0_();
        close token(P0_);
    }
}

@*/

void start()
    //@ requires module(buffered_io_start, true) &*& token(?P0) &*& beep_(P0, ?P1) &*& write_char_(P1, 'h', ?P2) &*& write_char_(P2, 'i', ?P3);
    //@ ensures module(buffered_io_start, false) &*& token(P3);
{
    //@ open_module();
    //@ stdio_init();
    //@ lift_beep_();
    //@ putchar__intro();
    //@ putchar__intro();
    //@ flush__intro(P3);
    main();
    //@ empty_stdout_buffer_token_elim(P3);
    //@ destroy_stdio();
    //@ close_module();
}
