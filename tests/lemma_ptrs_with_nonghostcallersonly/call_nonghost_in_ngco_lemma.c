/* error scenario of combining lemma pointers and nonghostcallers_only in C.
 * Call nonghost_callers_only lemma in a lemma function pointer chunk in
 * a nonghost_callers_only lemma.
*/


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


lemma void test()
  requires true;
  ensures true;
  {
    
         produce_lemma_function_pointer_chunk(empty) : empty_t()()
                {
                    normal_lemma(); // can call preceding lemmas.
                    nonghost_only_lemma();  //~  <-- must fail
                    call();
                    normal_lemma();
                }
                {
                    nonghost_only_lemma();
                }
    
  }

@*/
