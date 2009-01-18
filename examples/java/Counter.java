public class Counter {

  int value;

  Counter(int v)
    //@ requires emp;
    //@ ensures result.value |-> v;
  {
    this.value = v;
  }

  void increment()
    //@ requires this.value |-> ?v;
    //@ ensures this.value |-> v + 1;
  {
    this.value = this.value + 1;
  }

  static void swap(Counter c1, Counter c2)
    //@ requires c1.value |-> ?v1 &*& c2.value |-> ?v2;
    //@ ensures c1.value |-> v2 &*& c2.value |-> v1;
  {
    int tmp = c1.value;
    c1.value = c2.value;
    c2.value = tmp;
  }

  public static void main(String[] args)
    //@ requires true;
    //@ ensures true;
  {
    Counter c1 = new Counter(0);
    Counter c2 = new Counter(5);
    c1.increment();
    Counter.swap(c1, c2);
    int tmp = c2.value;
    //@ assert tmp == 1;
  }
}
