/*@

typedef lemma void predicate_value_implication<t>(predicate() helper, 
                                                  predicate(t) p1, 
                                                  predicate(t) p2)(t arg);
  requires helper() &*& p1(arg);
  ensures  p2(arg);

predicate dummy_helper() = true;

lemma void predicate_value_extensionality<t>(predicate(t) p1, predicate(t) p2);
  requires is_predicate_value_implication(?proof3, ?helper, p1, p2) &*&
           is_predicate_value_implication(?proof4, helper, p2, p1) &*& 
             helper();
  ensures  is_predicate_value_implication(proof3, helper, p1, p2) &*& 
           is_predicate_value_implication(proof4, helper, p2, p1) &*&
           p1 == p2;
@*/

//Lemma above is unsound
//----------------------

char x = 'x';

/*@

predicate p1(char* d) =
  character(&x, '0')
;

predicate p2(char* d) =
  true
;

predicate_ctor helper(int i)() =
  character(&x, '0')
;

lemma void transform<t>(predicate(t) p1, predicate(t) p2, t arg)
  requires p1(arg) &*& p1 == p2;
  ensures  p2(arg);
{
  assert true;
}

lemma void evil(char* c)
  requires character(&x, '0');
  ensures  character(&x, '0') &*&
           character(&x, '0');
{
  {
    lemma void impl1(char* d)
      requires helper(0)() &*& p1(d);
      ensures  p2(d);
    {
      leak p1(d);
      leak helper(0)();
      close p2(d);
    }
    lemma void impl2(char* d)
      requires helper(0)() &*& p2(d);
      ensures  p1(d);
    {
      open p2(d);
      open helper(0)();
      close p1(d);
    }
    produce_lemma_function_pointer_chunk(impl1) :
      predicate_value_implication<char*>
        (helper(0), p1, p2)(d){ call(); }
    {
      produce_lemma_function_pointer_chunk(impl2) :
        predicate_value_implication<char*>
          (helper(0), p2, p1)(d){ call(); }
      {
        close helper(0)();
        predicate_value_extensionality(p1, p2);
        assert p1 == p2;
        close p2(c);
        transform(p2, p1, c);
        close p2(c);
        transform(p2, p1, c);
        open p1(c);
        open p1(c);
      }
    }
  }
}

predicate hide(char* p, char c) =
  character(p, c)
;

@*/

int main() //@ : main_full(incorrect_predicate_value_extensionality)
  //@ requires module(incorrect_predicate_value_extensionality, true);
  //@ ensures true;
{
  //@ open_module();

  x = '0';
  //@ evil(&x);
  //@ close hide(&x, '0');
  x = '1';
  //@ close hide(&x, '1');
  //@ leak [1/2]hide(&x, '0');
  //@ leak [1/2]hide(&x, '1');
  //@ open [1/2]hide(&x, '0');
  //@ open [1/2]hide(&x, '1');
  
  //@ leak character(&x, '0');
  //@ assert false;
}

