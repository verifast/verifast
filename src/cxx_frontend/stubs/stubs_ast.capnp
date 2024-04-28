@0xdb4a8dae3cd61222;

using Cxx = import "/capnp/c++.capnp";
$Cxx.namespace("stubs");

struct Loc {
  struct SrcPos {
    l @0 :UInt16;
    c @1 :UInt16;
    fd @2 :UInt16;
  }

  struct Lexed {
    start @0 :SrcPos;
    end @1 :SrcPos;
  }

  struct MacroExp {
    callSite @0 :Loc;
    bodyToken @1 :Loc;
  }

  struct MacroParamExp {
    param @0 :Loc;
    argToken @1 :Loc;
  }

  union {
    unionNotInitialized @0 :Void;
    lexed @1 :Lexed;
    macroExp @2 :MacroExp;
    macroParamExp @3 :MacroParamExp;
  }
}

struct Node(Base) {
  loc @0 :Loc;
  desc @1 :Base;
}

struct Clause {
  loc @0 :Loc;
  text @1 :Text;
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

struct Param {
  type @0 :TypeNode;
  name @1 :Text; # optional
  default @2 :ExprNode; # optional
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

  struct FunctionProto {
    returnType @0 :TypeNode;
    ghostParams @1 :List(Clause); # should only be one clause
    params @2 :List(Param);
    contract @3 :List(Clause); # optional
  }

  union {
    unionNotInitialized @0 :Void;
    builtin @1 :BuiltinKind;
    pointer @2 :TypeNode;
    record @3 :RecordRef;
    enumType @4 :Text;
    lValueRef @5 :TypeNode;
    rValueRef @6 :TypeNode;
    fixedWidth @7 :FixedWidth;
    elaborated @8 :TypeNode;
    typedef @9 :Text;
    functionProto @10 :FunctionProto;
    substTemplateTypeParam @11 :TypeNode;
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

  struct For {
    init @0 :StmtNode;
    insideWhile @1 :While;
    iteration @2 :ExprNode;
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
    for @15 :For;
  }
}

struct Decl {

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
    struct BaseSpec {
      name @0 :Text;
      virtual @1 :Bool;
    }

    struct Body {
      decls @0 :List(DeclNode);
      bases @1 :List(Node(BaseSpec));
      polymorphic @2 :Bool;
      nonOverriddenMethods @3 :List(Text); # qualified names
      isAbstract @4 :Bool;
    }
    name @0 :Text;
    kind @1 :RecordKind;
    body @2 :Body; # optional
  }

  struct Method {
    struct Override {
      name @0 :Text; # qualified name
      base @1 :RecordRef;
    }

    static @0 :Bool;
    func @1 :Function;
    this @2 :Type; # optional, not present if it is a static method
    virtual @3 :Bool;
    overrides @4 :List(Override); # optional, only present if the method is virtual and overrides methods
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

  struct Namespace {
    name @0 :Text;
    decls @1 :List(DeclNode);
  }

  struct FunctionTemplate {
    name @0 :Text;
    specs @1 :List(Node(Function));
    contract @2 :List(Clause); # optional
  }

  isImplicit @0 :Bool;

  union {
    unionNotInitialized @1 :Void;
    ann @2 :Text;
    empty @3 :Void;
    var @4 :Var;
    function @5 :Function;
    field @6 :Field;
    record @7 :Record;
    method @8 :Method;
    accessSpec @9 :Void;
    ctor @10 :Ctor;
    dtor @11 :Dtor;
    typedef @12 :Typedef;
    enumDecl @13 :Enum;
    namespace @14 :Namespace;
    functionTemplate @15 :FunctionTemplate;
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
  character @3;
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

  struct ConditionalOp {
    cond @0 :ExprNode;
    then @1 :ExprNode;
    else @2 :ExprNode;
  }

  struct IntLit {
    uSuffix @0 :Bool;
    lSuffix @1 :SufKind;
    base @2 :NbBase;
    lowBits @3 :UInt64;
    highBits @4 :UInt64; # Reserved for future use with 128 Bit Integers
  }

  struct Call {
    args @0 :List(ExprNode);
    callee @1 :ExprNode;
  }

  struct MemberCall {
    implicitArg @0 :ExprNode;
    arrow @1 :Bool;
    call @2 :Call;
    targetHasQualifier @3 :Bool;
  }

  struct Member {
    base @0 :ExprNode;
    name @1 :Text;
    arrow @2 :Bool;
    baseIsPointer @3 :Bool;
  }

  struct New {
    type @0 :Type;
    expr @1 :ExprNode; # optional
  }

  struct Construct {
    name @0 :Text;
    args @1 :List(ExprNode);
    type @2 :Type;
  }

  struct Cast {
    expr @0 :ExprNode;
    type @1 :Type;
  }

  union {
    unionNotInitialized @0 :Void;
    unaryOp @1 :UnaryOp;
    binaryOp @2 :BinaryOp;
    boolLit @3 :Bool;
    intLit @4 :IntLit;
    stringLit @5 :Text;
    call @6 :Call;
    declRef @7 :Text;
    member @8 :Member;
    this @9 :Void;
    memberCall @10 :MemberCall;
    new @11 :New;
    construct @12 :Construct;
    nullPtrLit @13 :Void;
    delete @14 :ExprNode;
    truncating @15 :ExprNode;
    lValueToRValue @16 :ExprNode;
    derivedToBase @17 :Cast;
    baseToDerived @18 :Cast;
    operatorCall @19 :Call;
    cleanups @20 :ExprNode;
    bindTemporary @21 :ExprNode;
    integralCast @22 :Cast;
    conditionalOp @23 :ConditionalOp;
  }
}

struct Include {
  struct RealInclude {
    loc @0 :Loc;
    fileName @1 :Text; # as written in the include directive
    fd @2 :UInt16;
    includes @3 :List(Include);
    isAngled @4 :Bool;
  }

  union {
    unionNotInitialized @0 :Void;
    realInclude @1 :RealInclude;
    ghostInclude @2 :Clause;
  }
}

struct File {
  fd @0 :UInt16;
  path @1 :Text;
  decls @2 :List(DeclNode);
}

# A translation unit does not have a valid source location in Clang.
# That's why we don't encode it as a DeclNode.
struct TU {
  mainFd @0 :UInt16;
  files @1 :List(File);
  includes @2 :List(Include);
  failDirectives @3 :List(Clause);
}

struct Error {
  loc @0 :Loc;
  reason @1 :Text;
}

struct SerResult {
  tu @0 :TU;
  errors @1 :List(Error);
}
