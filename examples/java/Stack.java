class Node {

    int value;
    Node next;

}

/*@

predicate nodes(Node n0; int count) =
    n0 == null ?
        count == 0
    :
        n0.value |-> _ &*& n0.next |-> ?next &*&
        nodes(next, ?ncount) &*&
        count == 1 + ncount;

@*/

class Stack {

    Node head;
    
    //@ predicate valid(int count) = head |-> ?h &*& nodes(h, count);
    
    Stack()
        //@ requires true;
        //@ ensures valid(0);
    {
        //@ close valid(0);
    }
    
    void push(int element)
        //@ requires valid(?count);
        //@ ensures valid(count + 1);
    {
        //@ open valid(count);
        Node n = new Node();
        n.value = element;
        n.next = head;
        head = n;
        //@ close nodes(head, count + 1);
        //@ close valid(count + 1);
    }
    
    int pop()
        //@ requires valid(?count) &*& 0 < count;
        //@ ensures valid(count - 1);
    {
        //@ open valid(count);
        //@ open nodes(_, _);
        int result = head.value;
        head = head.next;
        //@ close valid(count - 1);
        return result;
    }

}

class Program {

    public static void main(String[] args)
        //@ requires true;
        //@ ensures true;
    {
        Stack s = new Stack();
        s.push(10);
        s.push(20);
        s.push(30);
        s.pop();
        s.pop();
        s.pop();
    }

}