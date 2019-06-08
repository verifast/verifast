//@ #include <list.gh>

/*@ 
    lemma void take_simple(list<int> xs) 
        requires true; 
        ensures take(0, xs) == nil; 
    {} 

    lemma void take_drop(list<int> xs) 
        requires true; 
        ensures take(0, drop(0, xs)) == nil; 
    {}

    lemma void take_drop_take(list<int> xs) 
        requires true; 
        ensures take(0, drop(0, take(length(xs), xs))) == nil; 
    {}
@*/