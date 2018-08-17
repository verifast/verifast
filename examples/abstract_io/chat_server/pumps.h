#ifndef PUMPS_H
#define PUMPS_H

#include "network.h"
#include "channels.h"

/*@

fixpoint list<char> quote(list<char> name, list<char> msg) {
    return append(name, append(" says ", msg));
}

@*/

char *create_quoted_msg(char *nick, char *msg);
    //@ requires [?f1]string(nick, ?nickChars) &*& [?f2]string(msg, ?msgChars);
    //@ ensures [f1]string(nick, nickChars) &*& [f2]string(msg, msgChars) &*& malloced_string(result, quote(nickChars, msgChars));

void pumpFromNick(channel roomChan, char *nick);
    /*@
    requires
        [_]string(nick, ?nickChars) &*& token(?R) &*& receiveFromNick_(R, nickChars, ?msgs) &*&
        token(?S) &*& send_(S, roomChan, malloced_string, (map_)((quote)(nickChars), msgs));
    @*/
    //@ ensures false;

#define NICK1 "Bert"
#define NICK2 "Ernie"

/*@

predicate_ctor pump_(predicate() S)(fixpoint(nat, list<char>) msgs) =
    split_(S, ?S1, ?S2)
    &*& sendToNick_(S1, NICK1, msgs)
    &*& sendToNick_(S2, NICK2, msgs);

@*/

void pumpRoom(channel roomChan);
    /*@
    requires
        receive_(?R, roomChan, malloced_string, ?msgs) &*& token(R) &*&
        token(?S) &*& pump_(S)(msgs);
    @*/
    //@ ensures false;

#endif
