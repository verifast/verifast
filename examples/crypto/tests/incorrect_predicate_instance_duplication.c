/*@

typedef lemma void duplication<t>(predicate(t) p)(t arg);
  requires [_]p(arg);
  ensures  p(arg);

lemma void duplication_duplication<t>(predicate(t) p);
  requires [_]is_duplication<t>(?proof, p);
  ensures  is_duplication<t>(proof, p);

@*/

//Lemma above is unsound
//----------------------

char x = 'x';

/*@

predicate evil(unit unit) = 
  is_duplication<unit>(mydup, evil) &*& character(&x, 'x')
;

lemma void mydup(unit unit)
requires [_]evil(unit);
ensures evil(unit);
{
   open [_]evil(unit);
   duplication_duplication(evil);
   assert is_duplication<unit>(?somefunc, evil);
   somefunc(unit);
   open evil(unit);
   close evil(unit);
   leak is_duplication<unit>(mydup, evil);
}

predicate hide(char* p, char c) =
  character(p, c)
;

@*/

int main() //@ : main_full(incorrect_predicate_instance_duplication)
  //@ requires module(incorrect_predicate_instance_duplication, true);
  //@ ensures true;
{
  //@ open_module();

  //@ produce_lemma_function_pointer_chunk(mydup) : duplication<unit>(evil)(u){ call(); };
  x = 'x';
  //@ close evil(unit);
  //@ leak evil(unit);
  //@ mydup(unit);
  //@ open evil(unit);
  x = 'y';
  //@ mydup(unit);
  //@ open evil(unit);
  
  //@ close hide(&x, 'x');
  //@ close hide(&x, 'y');
  //@ leak [1/2]hide(&x, 'x');
  //@ leak [1/2]hide(&x, 'y');
  //@ open [1/2]hide(&x, 'x');
  //@ open [1/2]hide(&x, 'y');
  
  //@ assert false;
}



