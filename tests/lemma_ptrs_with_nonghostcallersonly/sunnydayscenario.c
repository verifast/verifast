/* Sunny day scenario of combining lemma pointers and nonghostcallers_only in C */


/*@
typedef lemma void empty_t();
requires true;
ensures true;

lemma void empty()
requires true;
ensures true;
{
}

lemma void normal_lemma()
requires true;
ensures true;
{
}

lemma void nonghost_only_lemma()
nonghost_callers_only
requires true;
ensures true;
{
}
@*/

void test()
  //@ requires true;
  //@ ensures true;
  {
    /*@
         produce_lemma_function_pointer_chunk(empty) : empty_t()()
                {
                    normal_lemma(); // can call preceding lemmas.
                    call();
                    normal_lemma();
                }
                {
                    nonghost_only_lemma();
                }
    @*/
  }
