//@ #include <list.gh>

/*@ 
    lemma void dummy_function(int n, list<int> xs) 
        requires true; 
        ensures take(n, xs) == nil; 
    {} 
@*/