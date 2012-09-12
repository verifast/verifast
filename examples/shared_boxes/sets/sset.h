#ifndef SSET_H
#define SSET_H

//@ #include "slist.gh"

struct sset;

/*@

predicate sset(struct sset* s, list<int> vs);

@*/


struct sset* screate();
    //@requires true;
    //@ensures sset(result, nil);

void sdispose(struct sset* l);
    //@requires sset(l, ?vs);
    //@ensures true;

bool scontains(struct sset* l, int v);
    //@requires sset(l, ?vs) &*& v > INT_MIN &*& v < INT_MAX;
    //@ensures sset(l, vs) &*& result == mem(v, vs); 

void sadd(struct sset* l, int v);
    //@requires sset(l, ?vs) &*& v > INT_MIN &*& v < INT_MAX;
    //@ensures sset(l, sorted_insert(v, vs));

void sremove(struct sset* l, int v);
    //@requires sset(l, ?vs) &*& v > INT_MIN &*& v < INT_MAX;
    //@ensures sset(l, remove_all2(v, vs));



#endif 
