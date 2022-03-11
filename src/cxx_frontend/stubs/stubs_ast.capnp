@0xdb4a8dae3cd61222;

using Cxx = import "/capnp/c++.capnp";
$Cxx.namespace("stubs");

struct Loc {
  struct SrcPos {
    l @0 :UInt16;
    c @1 :UInt16;
    fd @2 :UInt16;
  }

  start @0 :SrcPos;
  end @1 :SrcPos;
}

struct Node(Base) {
  loc @0 :Loc;
  desc @1 :Base;
}

using StmtNode = Node(Stmt);
using DeclNode = Node(Decl);
using ExprNode = Node(Expr);
using TypeNode = Node(Type);
using AnnNode = Node(Text);

enum RecordKind {
  struc @0;
  class @1;
  unio @2;
}

struct RecordRef {
  name @0 :Text;
  kind @1 :RecordKind;
}

struct Type {
  enum BuiltinKind {
    char @0;
    uChar @1;
    short @2;
    uShort @3;
    void @4;
    bool @5;
    int @6;
    uInt @7;
    long @8;
    uLong @9;
    longLong @10;
    uLongLong @11;
  }

  struct FixedWidth {
    enum FixedWidthKind {
      int @0;
      uInt @1;
    }

    kind @0 :FixedWidthKind;
    bits @1 :UInt8;
  }

  union {
    unionNotInitialized @0 :Void;
    builtin @1 :BuiltinKind;
    pointer @2 :TypeNode;
    wPointer @3 :Type;
    record @4 :RecordRef;
    enumType @5 :Text;
    lValueRef @6 :TypeNode;
    wLValueRef @7 :Type;
    rValueRef @8 :TypeNode;
    wRValueRef @9 :Type;
    fixedWidth @10 :FixedWidth;
    elaborated @11 :TypeNode;
    wElaborated @12 :Type;
    typedef @13 :Text;
  }
}

struct Stmt {
  struct Return {
    expr @0 :ExprNode; # optional
  }

  struct If {
    cond @0 :ExprNode;
    then @1 :StmtNode;
    else @2 :StmtNode; #optional
  }

  struct Compound {
    stmts @0 :List(StmtNode);
    rBrace @1 :Loc;
  }

  struct While {
    cond @0 :ExprNode;
    body @1 :StmtNode;
    spec @2 :List(Clause);
    whileLoc @3 :Loc;
  }

  struct Case {
    lhs @0 :ExprNode;
    stmt @1 :StmtNode; # optional
  }

  struct DefCase {
    stmt @0 :StmtNode; # optional
  }

  struct Switch {
    cond @0 :ExprNode;
    cases @1 :List(StmtNode);
  }

  union {
    unionNotInitialized @0 :Void;
    ann @1 :Text;
    decl @2 :List(DeclNode);
    compound @3 :Compound;
    expr @4 :ExprNode;
    return @5 :Return;
    if @6 :If;
    null @7 :Void;
    while @8 :While;
    doWhile @9 :While;
    break @10 :Void;
    continue @11 :Void;
    switch @12 :Switch;
    case @13 :Case;
    defCase @14 :DefCase;
  }
}

struct Clause {
  loc @0 :Loc;
  text @1 :Text;
}

struct Decl {
  struct Param {
    type @0 :TypeNode;
    name @1 :Text;
    default @2 :ExprNode; # optional
  }

  struct Var {
    enum InitStyle {
      cInit @0;
      callInit @1;
      listInit @2;
    }
    struct VarInit {
      init @0 :ExprNode;
      style @1 :InitStyle;
    } 
    name @0 :Text;
    type @1 :TypeNode;
    init @2 :VarInit; # optional
  }

  struct Function {
    name @0 :Text;
    body @1 :StmtNode; # optional
    result @2 :TypeNode;
    params @3 :List(Param);
    contract @4 :List(Clause); # optional
    mangledName @5 :Text;
  }

  struct Field {
    enum InitStyle {
      copyInit @0;
      listInit @1;
    }
    struct FieldInit {
      init @0 :ExprNode;
      style @1 :InitStyle;
    }
    name @0 :Text;
    type @1 :TypeNode;
    init @2 :FieldInit; # optional
  }

  struct Record {
    struct Body {
      fields @0 :List(Node(Field));
      decls @1 :List(DeclNode);
    }
    name @0 :Text;
    kind @1 :RecordKind;
    body @2 :Body; # optional
  }

  struct Method {
    static @0 :Bool;
    func @1 :Function;
    this @2 :Type; # optional, not present if it is a static method
    implicit @3 :Bool;
  }

  struct Ctor {
    struct CtorInit {
      name @0 :Text;
      init @1 :ExprNode; # optional, not present when the default field initializer is used
      isWritten @2 :Bool;
    }
    method @0 :Method;
    initList @1 :List(CtorInit); # optional, not present if the constructor is not a definition
    parent @2 :RecordRef; # struct/class/union 
  }

  struct Dtor {
    method @0 :Method;
    parent @1 :RecordRef;
  }

  struct Typedef {
    type @0 :TypeNode;
    name @1 :Text;
  }

  struct Enum {
    struct EnumField {
      name @0 :Text;
      expr @1 :ExprNode; # optional
    }
    name @0 :Text;
    fields @1 :List(EnumField);
  }

  union {
    unionNotInitialized @0 :Void;
    ann @1 :Text;
    empty @2 :Void;
    var @3 :Var;
    function @4 :Function;
    field @5 :Field;
    record @6 :Record;
    method @7 :Method;
    accessSpec @8 :Void;
    ctor @9 :Ctor;
    dtor @10 :Dtor;
    typedef @11 :Typedef;
    enumDecl @12 :Enum;
  }
}

enum UnaryOpKind {
  plus @0;
  minus @1;
  not @2;
  lNot @3;
  addrOf @4;
  deref @5;
  preInc @6;
  preDec @7;
  postInc @8;
  postDec @9;
}

enum BinaryOpKind {
  add @0;
  sub @1;
  assign @2;
  mul @3;
  div @4;
  rem @5;
  shl @6;
  shr @7;
  lt @8;
  gt @9;
  le @10;
  ge @11;
  eq @12;
  ne @13;
  and @14;
  or @15;
  xor @16;
  lAnd @17;
  lOr @18;
  mulAssign @19;
  divAssign @20;
  remAssign @21;
  addAssign @22;
  subAssign @23;
  shlAssign @24;
  shrAssign @25;
  andAssign @26;
  xorAssign @27;
  orAssign @28;
}

enum SufKind {
  lSuf @0;
  lLSuf @1;
  noSuf @2;
}

enum NbBase {
  decimal @0;
  octal @1;
  hex @2;
}

struct Expr {
  struct UnaryOp {
    operand @0 :ExprNode;
    kind @1 :UnaryOpKind;
  }

  struct BinaryOp {
    lhs @0 :ExprNode;
    rhs @1 :ExprNode;
    kind @2 :BinaryOpKind;
  }

  struct IntLit {
    value @0 :Text;
    uSuffix @1 :Bool;
    lSuffix @2 :SufKind;
    base @3 :NbBase;
  }

  struct Call {
    args @0 :List(ExprNode);
    callee @1 :ExprNode;
  }

  struct Member {
    base @0 :ExprNode;
    name @1 :Text;
    arrow @2 :Bool;
    mangledName @3 :Text; #optional, present if it refers to a function/method
    baseIsPointer @4 :Bool;
    qualName @5 :Text;
  }

  struct New {
    type @0 :Type;
    expr @1 :ExprNode; # optional
  }

  struct DeclRef {
    name @0 :Text;
    mangledName @1 :Text; # optional, present if it refers to a function/method
    isClassMember @2 :Bool;
  }

  struct Construct {
    name @0 :Text;
    mangledName @1 :Text;
    args @2 :List(ExprNode);
    type @3 :Type;
  }

  union {
    unionNotInitialized @0 :Void;
    unaryOp @1 :UnaryOp;
    binaryOp @2 :BinaryOp;
    boolLit @3 :Bool;
    intLit @4 :IntLit;
    stringLit @5 :Text;
    call @6 :Call;
    declRef @7 :DeclRef;
    member @8 :Member;
    this @9 :Void;
    memberCall @10 :Call;
    new @11 :New;
    construct @12 :Construct;
    nullPtrLit @13 :Void;
    delete @14 :ExprNode;
    truncating @15 :ExprNode;
    lValueToRValue @16 :ExprNode;
  }
}

struct Include {
  loc @0 :Loc;
  fileName @1 :Text; # as written in the include directive
  fd @2 :UInt16;
  includes @3 :List(Include);
  isAngled @4 :Bool;
}

struct File {
  fd @0 :UInt16;
  path @1 :Text;
  decls @2 :List(DeclNode);
}

# A translation unit does not have a valid source location in Clang.
# That's why we don't use it as a DeclNode.
struct TU {
  mainFd @0 :UInt16;
  includes @1 :List(Include);
  files @2 :List(File);
}

struct Err {
  loc @0 :Loc;
  reason @1 :Text;
}

struct SerResult {
  union {
    ok @0 :Void;
    err @1 :Void;
  }
}