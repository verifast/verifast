/*@
typedef lemma void quux()();
    requires true;
    ensures true;
@*/

void foo()
   //@ requires true;
   //@ ensures true;
{
    {
        /*@
        lemma void bar()
            requires true;
            ensures true;
        {}
        @*/
        
        /*@
        produce_lemma_function_pointer_chunk(bar) : quux()() { bar(); call(); } {}
        @*/
    }
}