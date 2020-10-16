// Bart Jacobs. Modular Verification of Liveness Properties of the I/O Behavior of Imperative Programs. At ISoLA 2020.

struct message;
typedef struct message *message;

//@ predicate message(message message; int id);

//@ predicate receive_(predicate() P, int messageId, predicate() Q);
//@ predicate send_(predicate() P, int messageId, predicate() Q);

message receive();
//@ requires receive_(?P, ?id, ?Q) &*& P();
//@ ensures message(result, id) &*& Q();
//@ terminates;

void send(message message);
//@ requires message(message, ?id) &*& send_(?P, id, ?Q) &*& P();
//@ ensures Q();
//@ terminates;

/*@

fixpoint int tail_(fixpoint(int, int) seq, int i) { return seq(i + 1); }

copredicate receive_all(predicate() P, fixpoint(int, int) ms) =
  receive_(P, ms(0), ?Q) &*&
  receive_all(Q, (tail_)(ms));
  
predicate False() = false;

copredicate send_all(predicate() P, fixpoint(int, int) ms, int k) =
  send_(P, ms(0), ?Q) &*& k == 0 ? Q == False : send_all(Q, (tail_)(ms), k - 1);

@*/

int main() //@ : custom_main_spec
//@ requires receive_all(?Pr, ?ms) &*& send_all(?Ps, ms, ?k) &*& Pr() &*& Ps() &*& 0 <= k;
//@ ensures false;
//@ terminates;
{
  for (;;)
  //@ invariant receive_all(?Pr1, ?ms1) &*& send_all(?Ps1, ms1, ?k1) &*& Pr1() &*& Ps1() &*& 0 <= k1;
  //@ decreases k1;
  {
    //@ open receive_all(Pr1, ms1);
    //@ open send_all(Ps1, ms1, k1);
    message m = receive();
    send(m);
    //@ if (k1 == 0) open False();
  }
}
