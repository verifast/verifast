/*@

inductive nodeIn = parentIn(list<nodeIn>) | leafIn;

inductive nodeOut = parentOut(list<nodeOut>) | leafOut;

fixpoint nodeOut getOut(nodeIn n) {
    switch(n) {
        case parentIn(l): return parentOut(map(getOut, l));
        case leafIn: return leafOut;
    }
}

@*/
