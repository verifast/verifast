//@ predicate a(boolean x; int y) = x ? b(0, 0, 0, y) : y == 0;
//@ predicate b<t1, t2>(t1 x, t1 y, t2 z1; t2 z2) = x == y ? c<t1, t2>(x, z2) : z2 == z1;
//@ predicate c<tp1, tp2>(tp1 x; tp2 y);

//@ predicate n(;);
//@ predicate p(;) = [1/2]n();

class Automation {
  void test1() 
    //@ requires a(true, 5);
    //@ ensures true;
  {
    //@ assert c(0, 5);
  }
  
  void test2()
    //@ requires p();
    //@ ensures true;
  {
     //@ assert [1/2]n();
  }
}

/*@
predicate_family cell(Class c)(Cell c;);

predicate_family_instance cell(CellImpl.class)(CellImpl c) = c.value |-> _;
predicate_family_instance cell(BackupCell.class)(BackupCell c) = cell(CellImpl.class)(c);
predicate_family_instance cell(BackupCellWrapper.class)(BackupCellWrapper c) = c.b |-> ?b &*& b ? c.myvalue |-> _ : cell(BackupCell.class)(c);
@*/
interface Cell {
}

class CellImpl implements Cell {
  int value;
}

class BackupCell extends CellImpl {
}

class BackupCellWrapper extends CellImpl {
  boolean b;
  int myvalue;
}

class Test {
  void test1(CellImpl c) 
    //@ requires cell(BackupCell.class)(c);
    //@ ensures true;
  {
    c.value = 5;
  }
  
  void test2(BackupCellWrapper c) 
    //@ requires cell(BackupCellWrapper.class)(c);
    //@ ensures true;
  {
    if(! c.b) {
      c.value = 5;
    } else {
      c.myvalue = 10;
    }
  }
}
