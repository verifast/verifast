class Shape
{
  int m_x;
  int m_y;

public:
  Shape(int x, int y) : m_x(x), m_y(y)
  //@ requires true;
  /*@ ensures
      Shape_vtype(this, &typeid(struct Shape)) &*&
      this->m_x |-> x &*& 
      this->m_y |-> y;
  @*/
  {}

  virtual ~Shape()
  /*@ requires
      Shape_vtype(this, &typeid(struct Shape)) &*&
      this->m_x |-> _ &*&
      this->m_y |-> _;
  @*/
  //@ ensures true;
  {}

  virtual int calcArea() const = 0;
  //@ requires true;
  //@ ensures true;
};

class Square : public Shape
{
  int m_w;

public:
  Square(int x, int y, int w) : Shape(x, y), m_w(w)
  //@ requires true;
  /*@ ensures
      Square_vtype(this, &typeid(struct Square)) &*&
      Square_bases_constructed(this) &*&
      Shape_m_x(this, x) &*&
      Shape_m_y(this, y) &*&
      this->m_w |-> w;
  @*/
  {}

  ~Square()
  /*@ requires
      Square_vtype(this, &typeid(struct Square)) &*&
      Square_bases_constructed(this) &*&
      Shape_m_x(this, _) &*&
      Shape_m_y(this, _) &*&
      this->m_w |-> _; 
  @*/
  //@ ensures true;
  {}

  int calcArea() const override //~
  //@ requires Square_bases_constructed(this) &*& this->m_w |-> ?w;
  //@ ensures Square_bases_constructed(this) &*& this->m_w |-> w; 
  {
    return m_w * m_w;
  }
};