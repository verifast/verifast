class Pos
{
  int m_x;
  int m_y;

public:
  /*@ 
    predicate valid(int x, int y) =
      this->m_x |-> x &*& this->m_y |-> y;
  @*/

  Pos(int x, int y) : m_x(x), m_y(y) 
  //@ requires true;
  //@ ensures valid(x, y);
  {
    //@ close valid(x, y);
  }

  Pos() : Pos(0, 0)
  //@ requires true;
  //@ ensures valid(0, 0);
  {}

  Pos(const Pos &pos) : Pos(pos.getX(), pos.getY())
  //@ requires pos.valid(?x, ?y);
  //@ ensures valid(x, y) &*& pos.valid(x, y);
  {}

  ~Pos()
  //@ requires valid(_, _);
  //@ ensures true;
  {
    //@ open valid(_, _);
  }

  int getX() const
  //@ requires valid(?x, ?y);
  //@ ensures valid(x, y) &*& result == x;
  {
    //@ open valid(x, y);
    return m_x;
    //@ close valid(x, y);
  }

  int getY() const
  //@ requires valid(?x, ?y);
  //@ ensures valid(x, y) &*& result == y;
  {
    //@ open valid(x, y);
    return m_y;
    //@ close valid(x, y);
  }

  void setX(int x)
  //@ requires valid(_, ?y);
  //@ ensures valid(x, y);
  {
    //@ open valid(_, y);
    m_x = x;
    //@ close valid(x, y);
  }

  void setY(int y)
  //@ requires valid(?x, _);
  //@ ensures valid(x, y);
  {
    //@ open valid(x, _);
    m_y = y;
    //@ close valid(x, y);
  }

  void moveTo(int x, int y)
  //@ requires valid(_, _);
  //@ ensures valid(x, y);
  {
    setX(x);
    setY(y);
  }

  void moveTo(const Pos &p)
  //@ requires valid(_, _) &*& p.valid(?x, ?y);
  //@ ensures valid(x, y) &*& p.valid(x, y);
  {
    int px = p.getX();
    int py = p.getY();
    moveTo(px, py);
  }
};

class Shape
{
  Pos m_pos;

public:
  /*@
    predicate valid(int x, int y) =
      struct_Pos_padding(&this->m_pos) &*&
      (&this->m_pos)->valid(x, y);
  @*/

  Shape(const Pos &pos) : m_pos(pos)
  //@ requires pos.valid(?x, ?y);
  //@ ensures pos.valid(x, y) &*& valid(x, y) &*& Shape_vtype(this, thisType);
  {
    //@ close valid(x, y);
  }

  virtual ~Shape()
  //@ requires valid(_, _) &*& Shape_vtype(this, thisType);
  //@ ensures true;
  {
    //@ open valid(_, _);
  }

  virtual int calcArea() const = 0;
  //@ requires valid(?x, ?y);
  //@ ensures valid(x, y) &*& result >= 0;
};

class Square : public Shape
{
  int m_width;

public:
  /*@
    predicate valid(int x, int y) =
      this->valid(&typeid(Shape))(x, y) &*&
      this->m_width |-> ?w &*&
      w >= 0 &*&
      Square_bases_constructed(this);
  @*/

  Square(const Pos &pos, int width) : Shape(pos), m_width(width)
  //@ requires pos.valid(?x, ?y) &*& width >= 0;
  //@ ensures valid(x, y) &*& pos.valid(x, y) &*& Square_vtype(this, thisType);
  {
    //@ close valid(x, y);
  }

  ~Square()
  //@ requires valid(_, _) &*& Square_vtype(this, thisType);
  //@ ensures true;
  {
    //@ open valid(_, _);
  }

  int calcArea() const override
  //@ requires valid(?x, ?y);
  //@ ensures valid(x, y) &*& result >= 0;
  {
    //@ open valid(x, y);
    return m_width * m_width;
    //@ mul_mono_l(0, this->m_width, this->m_width);
    //@ close valid(x, y);
  }
};

class Rectangle : public Shape
{
  int m_width;
  int m_height;

public:
  /*@
    predicate valid(int x, int y) =
      this->valid(&typeid(Shape))(x, y) &*&
      this->m_width |-> ?w &*& w >= 0 &*&
      this->m_height |-> ?h &*& h >= 0 &*&
      Rectangle_bases_constructed(this);
  @*/

  Rectangle(const Pos &pos, int width, int height) : Shape(pos), m_width(width), m_height(height)
  //@ requires pos.valid(?x, ?y) &*& width >= 0 &*& height >= 0;
  //@ ensures pos.valid(x, y) &*& valid(x, y) &*& Rectangle_vtype(this, thisType);
  {
    //@ close valid(x, y);
  }

  ~Rectangle()
  //@ requires valid(_, _) &*& Rectangle_vtype(this, thisType);
  //@ ensures true;
  {
    //@ open valid(_, _);
  }

  int calcArea() const override
  //@ requires valid(?x, ?y);
  //@ ensures valid(x, y) &*& result >= 0;
  {
    //@ open valid(x, y);
    return m_width * m_height;
    //@ mul_mono_l(0, this->m_width, this->m_height);
    //@ close valid(x, y);
  }
};

int calcArea(const Shape &s)
//@ requires s.valid(?x, ?y);
//@ ensures s.valid(x, y);
{
  return s.calcArea();
}

void destroy(Shape *s)
//@ requires s->valid(_, _) &*& new_block_Shape(s);
//@ ensures true;
{
  delete s;
}

/*@
predicate hide_Square_vtype(Square *s) = Square_vtype(s, &typeid(Square));
predicate hide_Shape_vtype(Rectangle *r) = Rectangle_vtype(r, &typeid(Rectangle));
@*/

int main()
//@ requires true;
//@ ensures true;
{
  Pos p;
  Square sq(p, 4);
  Rectangle rec(p, 8, 2);

  sq.calcArea();
  rec.calcArea();

  calcArea(sq);
  calcArea(rec);
  
  // hide vtypes, show that they are not needed for statically bound calls to virtual methods
  //@ close hide_Square_vtype(&sq);
  //@ close hide_Shape_vtype(&rec);
  sq.Square::calcArea();
  rec.Rectangle::calcArea();
  //@ open hide_Square_vtype(&sq);
  //@ open hide_Shape_vtype(&rec);
}