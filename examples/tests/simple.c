//@ #include <list.gh>

/*@ 
    lemma void dummy_function(list<int> xs) 
        requires true; 
        ensures take(0, xs) == nil; 
    {} 
@*/