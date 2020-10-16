// Willem Penninckx, Amin Timany, and Bart Jacobs. Specifying I/O using Abstract Nested Hoare Triples in Separation Logic. At FTfJP 2019.

struct message;
typedef struct message *message;

//@ predicate message(message message; int id);

//@ predicate receive_(predicate() P, int messageId, predicate() Q);
//@ predicate send_(predicate() P, int messageId, predicate() Q);

message receive();
//@ requires receive_(?P, ?id, ?Q) &*& P();
//@ ensures message(result, id) &*& Q();

void send(message message);
//@ requires message(message, ?id) &*& send_(?P, id, ?Q) &*& P();
//@ ensures Q();

/*@

fixpoint int tail_(fixpoint(int, int) seq, int i) { return seq(i + 1); }

copredicate receive_all(predicate() P, fixpoint(int, int) ms) =
  receive_(P, ms(0), ?Q) &*&
  receive_all(Q, (tail_)(ms));

copredicate send_all(predicate() P, fixpoint(int, int) ms) =
  send_(P, ms(0), ?Q) &*&
  send_all(Q, (tail_)(ms));

@*/

int main() //@ : custom_main_spec
//@ requires receive_all(?Pr, ?ms) &*& send_all(?Ps, ms) &*& Pr() &*& Ps();
//@ ensures false;
{
  for (;;)
  //@ invariant receive_all(?Pr1, ?ms1) &*& send_all(?Ps1, ms1) &*& Pr1() &*& Ps1();
  {
    //@ open receive_all(Pr1, ms1);
    //@ open send_all(Ps1, ms1);
    message m = receive();
    send(m);
  }
}
