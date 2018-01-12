#ifndef NETWORK_H
#define NETWORK_H

//@ #include "abstract_io.gh"
//@ #include "sequences.gh"

//@ predicate malloced_string(char *s; list<char> cs) = string(s, cs) &*& malloc_block(s, length(cs) + 1);

//@ predicate receiveFromNick_(predicate() P, list<char> nick, fixpoint(nat, list<char>) msgs);

char *receiveFromNick(char *nick);
    //@ requires [_]string(nick, ?nickChars) &*& token(?P) &*& receiveFromNick_(P, nickChars, ?msgs);
    //@ ensures malloced_string(result, msgs(zero)) &*& token(?P1) &*& receiveFromNick_(P1, nickChars, (tail_)(msgs));

//@ predicate sendToNick_(predicate() P, list<char> nick, fixpoint(nat, list<char>) msgs);

void sendToNick(char *nick, char *msg);
    //@ requires [_]string(nick, ?nickChars) &*& sendToNick_(?P, nickChars, ?msgs) &*& token(P) &*& [?f]string(msg, msgs(zero));
    //@ ensures token(?P1) &*& sendToNick_(P1, nickChars, (tail_)(msgs)) &*& [f]string(msg, msgs(zero));

#endif
