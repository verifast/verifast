#include <stdlib.h>
#include <threading.h>
#include "channels_local.h"
#include "pumps.h"

typedef struct pumpFromNick_closure {
    channel roomChan;
    char *nick;
} *pumpFromNick_closure;

/*@

predicate_family_instance thread_run_data(pumpFromNick_thunk)(pumpFromNick_closure closure) =
    closure->roomChan |-> ?rc &*& closure->nick |-> ?nick &*& malloc_block_pumpFromNick_closure(closure) &*&
    [_]string(nick, ?nickChars) &*& receiveFromNick_(?R, nickChars, ?msgs) &*& token(R) &*&
    send_(?S, rc, malloced_string, (map_)((quote)(nickChars), msgs)) &*& token(S);

@*/

void pumpFromNick_thunk(pumpFromNick_closure closure) //@ : thread_run
    //@ requires thread_run_data(pumpFromNick_thunk)(closure);
    //@ ensures true;
{
    //@ open thread_run_data(pumpFromNick_thunk)(closure);
    channel roomChan = closure->roomChan;
    char *nick = closure->nick;
    free(closure);
    pumpFromNick(roomChan, nick);
}

void pumpFromNick_async(channel roomChan, char *nick)
    /*@
    requires
        [_]string(nick, ?nickChars) &*& receiveFromNick_(?R, nickChars, ?msgs) &*& token(R) &*&
        send_(?S, roomChan, malloced_string, (map_)((quote)(nickChars), msgs)) &*& token(S);
    @*/
    //@ ensures true;
{
    pumpFromNick_closure closure = malloc(sizeof(struct pumpFromNick_closure));
    if (closure == 0) abort();
    closure->roomChan = roomChan;
    closure->nick = nick;
    //@ close thread_run_data(pumpFromNick_thunk)(closure);
    thread_start(pumpFromNick_thunk, closure);
}

channel create_channel_two_senders()
    //@ requires exists<pair<fixpoint(nat, T), fixpoint(nat, T)> >(pair(?msgs1, ?msgs2)) &*& exists<predicate(void *; T)>(?msgPred);
    /*@
    ensures
        send_(?S1, result, msgPred, msgs1) &*& token(S1) &*&
        send_(?S2, result, msgPred, msgs2) &*& token(S2) &*&
        receive_(?R, result, msgPred, ?msgs) &*& token(R) &*& is_interleaving(msgs1, msgs2, msgs) == true;
    @*/
{
    //@ is_interleaving_trivial1(msgs1, msgs2);
    //@ close create_channel_ghost_args((is_interleaving)(msgs1, msgs2), msgs1, msgPred);
    return create_channel();
    //@ get_forall_t<triple<fixpoint(nat, list<char>)> >();
    //@ assert [_]is_forall_t(?forall_triples);
    /*@
    if (!forall_triples((contains_interleavings_)((is_interleaving)(msgs1, msgs2), (eq)(msgs1), (eq)(msgs2)))) {
        triple<fixpoint(nat, list<char>)> seqs = not_forall_t(forall_triples, (contains_interleavings_)((is_interleaving)(msgs1, msgs2), (eq)(msgs1), (eq)(msgs2)));
        assert seqs == triple(?msgs1_, ?msgs2_, ?msgs3_);
        if (msgs1 == msgs1_ && msgs3_ == msgs1_) {
        } else if (msgs2 == msgs2_ && msgs3_ == msgs2_) {
            is_interleaving_trivial2(msgs1, msgs2_);
        } else {
        }
    }
    @*/
    //@ close contains_interleavings((is_interleaving)(msgs1, msgs2), (eq)(msgs1), (eq)(msgs2));
    //@ channel_sender_split((eq)(msgs1), (eq)(msgs2));
    //@ channel_sender_to_send_((eq)(msgs1), msgs1);
    //@ channel_sender_to_send_((eq)(msgs2), msgs2);
    //@ channel_receiver_to_receive_();
}

int main() //@ : custom_main_spec
    /*@
    requires
        token(?R1) &*& receiveFromNick_(R1, NICK1, ?msgs1) &*&
        token(?R2) &*& receiveFromNick_(R2, NICK2, ?msgs2) &*&
        token(?S) &*& bigsep((is_interleaving)((map_)((quote)(NICK1), msgs1), (map_)((quote)(NICK2), msgs2)), pump_(S));
    @*/
    //@ ensures false;
{
    //@ close exists(pair((map_)((quote)(NICK1), msgs1), (map_)((quote)(NICK2), msgs2)));
    //@ close exists(malloced_string);
    channel roomChan = create_channel_two_senders();
    //@ assert receive_(_, roomChan, _, ?msgs);
        
    pumpFromNick_async(roomChan, NICK1);
    pumpFromNick_async(roomChan, NICK2);
    
    //@ bigsep_extract(msgs);
    pumpRoom(roomChan);
    return 0;
}
