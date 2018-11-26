#include <stdlib.h>
#include <string.h>
#include "network.h"
#include "channels.h"
#include "pumps.h"
//@ #include <listex.gh>

char *create_quoted_msg(char *nick, char *msg)
    //@ requires [?f1]string(nick, ?nickChars) &*& [?f2]string(msg, ?msgChars);
    //@ ensures [f1]string(nick, nickChars) &*& [f2]string(msg, msgChars) &*& malloced_string(result, quote(nickChars, msgChars));
{
    size_t nickLen = strlen(nick);
    size_t msgLen = strlen(msg);
    if ((size_t)INT_MAX - 7 < nickLen || (size_t)INT_MAX - 7 - nickLen < msgLen) abort();
    char *result = malloc(nickLen + 6 + msgLen + 1);
    if (result == 0) abort();
    memcpy(result, nick, (unsigned)nickLen);
    char *says = " says ";
    //@ string_to_body_chars(says);
    memcpy(result + nickLen, says, 6);
    memcpy(result + nickLen + 6, msg, (unsigned)msgLen);
    //@ chars_join(result + nickLen);
    //@ chars_join(result);
    //@ body_chars_to_string(nick);
    result[nickLen + 6 + msgLen] = 0;
    return result;
}

void pumpFromNick(channel roomChan, char *nick)
    /*@
    requires
        [_]string(nick, ?nickChars) &*& token(?R) &*& receiveFromNick_(R, nickChars, ?msgs) &*&
        token(?S) &*& send_(S, roomChan, malloced_string, (map_)((quote)(nickChars), msgs));
    @*/
    //@ ensures false;
{
    for (;;)
        /*@
        invariant
            [_]string(nick, nickChars) &*& receiveFromNick_(?R0, nickChars, ?msgs0) &*& token(R0) &*&
            send_(?S0, roomChan, malloced_string, (map_)((quote)(nickChars), msgs0)) &*& token(S0);
        @*/
    {
        char *msg = receiveFromNick(nick);
        char *quotedMsg = create_quoted_msg(nick, msg);
        free(msg);
        
        channel_send(roomChan, quotedMsg);
        //@ tail__map((quote)(nickChars), msgs0);
    }
}

void pumpRoom(channel roomChan)
    /*@
    requires
        receive_(?R, roomChan, malloced_string, ?msgs) &*& token(R) &*&
        token(?S) &*& pump_(S)(msgs);
    @*/
    //@ ensures false;
{
    //@ open pump_(S)(msgs);
    //@ do_split();
    for (;;)
        /*@
        invariant
            receive_(?R0, roomChan, malloced_string, ?msgs0) &*& token(R0) &*&
            sendToNick_(?S1, NICK1, msgs0) &*& token(S1) &*&
            sendToNick_(?S2, NICK2, msgs0) &*& token(S2);
        @*/
    {
        char *msg = channel_receive(roomChan);
        sendToNick(NICK1, msg);
        sendToNick(NICK2, msg);
        free(msg);
    }
}
