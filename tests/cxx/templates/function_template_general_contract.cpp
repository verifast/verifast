struct ShortPoint
{
  short m_x;
  short m_y;
  
  ShortPoint(short x, short y) : m_x(x), m_y(y)
  //@ requires true;
  //@ ensures this->m_x |-> x &*& this->m_y |-> y;
  {}
  
  ~ShortPoint()
  //@ requires this->m_x |-> _ &*& this->m_y |-> _;
  //@ ensures true;
  {}
};

struct IntPoint
{
  int m_x;
  int m_y;
  
  IntPoint(int x, int y) : m_x(x), m_y(y)
  //@ requires true;
  //@ ensures this->m_x |-> x &*& this->m_y |-> y;
  {}
  
  ~IntPoint()
  //@ requires this->m_x |-> _ &*& this->m_y |-> _;
  //@ ensures true;
  {}
};

template<class T>
void swap(T *a, T *b)
//@ requires *a |-> ?x &*& *b |-> ?y;
//@ ensures *a |-> y &*& *b |-> x;
{
  T temp = *a;
  *a = *b;
  *b = temp;
}

template<class T>
void mirror(T *t)
//@ requires t->m_x |-> ?x &*& t->m_y |-> ?y;
//@ ensures t->m_x |-> y &*& t->m_y |-> x;
{
  swap(&t->m_x, &t->m_y);
}

int main()
//@ requires true;
//@ ensures true;
{
  ShortPoint sp(0, 1);
  IntPoint ip(2, 3);
  mirror(&sp);
  mirror(&ip);
}
