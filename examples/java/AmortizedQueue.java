/*@
predicate linkedlist(LinkedList l, list<int> vs) =
  l != null &*&
  [_]l.head |-> ?head &*&
  [_]l.tail |-> ?tail &*&
  [_]l.length |-> ?length &*&
  (tail == null ? vs == nil :
  linkedlist(tail, ?vs2) &*& vs == cons(head, vs2)) &*&
  length(vs) == length;
  
lemma void copy(LinkedList l)
  requires linkedlist(l, ?vs);
  ensures linkedlist(l, vs) &*& linkedlist(l, vs);
{
  open linkedlist(l, vs);
  if(l.tail == null) {

  } else {
    copy(l.tail);
  }
  close linkedlist(l, vs);
  close linkedlist(l, vs);
}
@*/

class LinkedList {
  int head;
  LinkedList tail;
  int length;
  
  public LinkedList() 
    //@ requires true;
    //@ ensures this.head |-> 0 &*& this.tail |-> null &*& this.length |-> 0;
  {
    
  }
  
  public static LinkedList New()
    //@ requires true;
    //@ ensures result != null &*& linkedlist(result, nil);
  {
    LinkedList l = new LinkedList();
    //@ leak l.head |-> _;
    //@ leak l.tail |-> null;
    //@ leak l.length |-> 0;
    //@ close linkedlist(l, nil);
    return l;
  }
  
  public LinkedList Cons(int d)    //@ requires linkedlist(this, ?vs);
    //@ ensures result != null &*& linkedlist(this, vs) &*& linkedlist(result, cons(d, vs));
  {
    //@ copy(this);
    //@ open linkedlist(this, vs);
    LinkedList r = new LinkedList();
    r.head = d;
    r.tail = this;
    r.length = length+1;
    //@ close linkedlist(this, vs);
    //@ leak r.head |-> d;
    //@ leak r.tail |-> _;
    //@ leak r.length |-> _;
    //@ close linkedlist(r, cons(d, vs));
    return r;
  }
  
  public LinkedList Concat(LinkedList end)
    //@ requires linkedlist(this, ?vs) &*& linkedlist(end, ?vs2);
    //@ ensures result != null &*& linkedlist(this, vs) &*& linkedlist(end, vs2) &*& linkedlist(result, append(vs, vs2));
  {
    //@ open linkedlist(this,vs);
    if(length == 0) {
      //@ copy(end);
      //@ open linkedlist(end, vs2);
      //@ close linkedlist(end, vs2);
      return end;
      //@ close linkedlist(this,vs);
    } else {
      LinkedList c = tail.Concat(end);
      LinkedList r = c.Cons(head);
      //@ close linkedlist(this,vs);
      return r;
    }
  }
  
  public LinkedList reverse()
    //@ requires linkedlist(this, ?vs);
    //@ ensures result != null &*& linkedlist(this, vs) &*& linkedlist(result, reverse(vs));
  {
    //@ open linkedlist(this, vs);
    LinkedList r;
    if(length == 0) {
      r = New();
    } else {
      r = tail.reverse();
      LinkedList e = New();
      e = e.Cons(head);
      r = r.Concat(e);
    }
    //@ close linkedlist(this, vs);
    return r;
  }
}

/*@
predicate queue(AmortizedQueue q, list<int> vs) =
  q != null &*& q.front |-> ?front &*& q.rear |-> ?rear &*& linkedlist(front, ?vs1) &*& linkedlist(rear, ?vs2) &*& vs == append(vs1, reverse(vs2)) &*& length(vs2) <= length(vs1);
@*/

class AmortizedQueue {
  LinkedList front;
  LinkedList rear;
  
  AmortizedQueue() 
    //@ requires true;
    //@ ensures queue(this, nil);
  {
    front = LinkedList.New();
    rear = LinkedList.New();
    //@ close queue(this, nil);
  }
  
  AmortizedQueue(LinkedList front, LinkedList rear) 
    //@ requires linkedlist(front, ?vs1) &*& linkedlist(rear, ?vs2);
    //@ ensures queue(this, append(vs1, reverse(vs2))) &*& linkedlist(front, vs1) &*& linkedlist(rear, vs2);
  {
    //@ copy(front);
    //@ copy(rear);
    //@ open linkedlist(front, vs1);
    //@ open linkedlist(rear, vs2);
    if(rear.length <= front.length) {
      this.front = front;
      this.rear = rear;
    } else {
      LinkedList f = rear.reverse();
      this.front = front.Concat(f);
      this.rear = LinkedList.New();
    }
    //@ close linkedlist(front, vs1);
    //@ close linkedlist(rear, vs2);
    //@ close queue(this, append(vs1, reverse(vs2)));
  }

  int front()
    //@ requires queue(this, ?vs) &*& vs != nil;
    //@ ensures queue(this, vs) &*& result == head(vs);
  {
    //@ open queue(this, vs);
    //@ LinkedList front = this.front;
    //@ LinkedList rear = this.rear;
    //@ open linkedlist(front, ?vs1);
    //@ open linkedlist(rear, ?vs2);
    int r = this.front.head;
    //@ close linkedlist(front, vs1);
    //@ close linkedlist(rear, vs2);
    //@ close queue(this, vs);
    return r;
  }
  
  AmortizedQueue tail() 
    //@ requires queue(this, ?vs) &*& vs != nil;
    //@ ensures queue(this, vs) &*& queue(result, tail(vs));
  {
    //@ open queue(this, vs);
    //@ LinkedList front = this.front;
    //@ LinkedList rear = this.rear;
    //@ open linkedlist(front, ?vs1);
    //@ open linkedlist(rear, ?vs2);
    //@ close linkedlist(rear, vs2);
    AmortizedQueue r = new AmortizedQueue(this.front.tail, this.rear);
    //@ close linkedlist(front, vs1);
    //@ close queue(this, vs);
    return r;
  }
  
  AmortizedQueue enqueue(int item)
    //@ requires queue(this, ?vs);
    //@ ensures result != null &*& queue(this, vs) &*& queue(result, append(vs, cons(item, nil)));
  {
    //@ open queue(this, vs);
    //@ LinkedList rear2 = this.rear;
    //@ open linkedlist(rear2, ?vs2);
    //@ close linkedlist(rear2, vs2);
    //@ LinkedList front = this.front;
    //@ open linkedlist(front, ?vs1);
    //@ close linkedlist(front, vs1);
    LinkedList r = rear.Cons(item);
    AmortizedQueue q = new AmortizedQueue(this.front, r);
    //@ append_assoc(vs1, reverse(vs2), cons(item, nil));
    //@ close queue(this, vs);
    return q;
  }
}

class Program {
  public static void main(String[] args) 
    //@ requires true;
    //@ ensures true;
  {
    AmortizedQueue q1 = new AmortizedQueue();
    AmortizedQueue q2 = q1.enqueue(5);
    AmortizedQueue q3 = q1.enqueue(6);
    int res1 = q2.front();
    int res2 = q3.front();
    assert(res1 == 5);
    assert(res2 == 6);
  }
}