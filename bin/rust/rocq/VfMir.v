From Coq Require Export List String NArith.
Export ListNotations.

Open Scope string_scope.

Inductive IntTy :=
| Isize
| I8
| I16
| I32
| I64
| I128
.

Inductive UintTy :=
| Usize
| U8
| U16
| U32
| U64
| U128
.

Inductive Ty :=
| Bool
| Char
| Int(ty: IntTy)
| Uint(ty: UintTy)
| RawPtr(ty: Ty)
| FnDef(id: string)(generic_args: list GenericArg)
| Never
| Tuple0
with GenericArg :=
| Type_(ty: Ty)
.

Inductive Mutability :=
| Not
| Mut
.

Definition Local := string.

Record LocalDecl := {
    mutability: Mutability;
    ty: Ty;
}.

Inductive PlaceExprElem :=
| Deref
.

Definition PlaceExpr: Set := Local * list PlaceExprElem.

Inductive ConstValue :=
| ZeroSized
.

Inductive ConstOperand :=
| Val(value: ConstValue)(ty: Ty)
.

Inductive Operand :=
| Move(place: PlaceExpr)
| Copy(place: PlaceExpr)
| Constant(const: ConstOperand)
.

Inductive CastKind :=
| PointerExposeProvenance
| PointerWithExposedProvenance
| PointerCoercion
| IntToInt
| FloatToInt
| FloatToFloat
| IntToFloat
| PtrToPtr
| FnPtrToPtr
| Transmute
| Subtype
.

Inductive Rvalue :=
| Use(operand: Operand)
| RawPtr_(place: PlaceExpr)
| Cast(kind: CastKind)(operand: Operand)(ty: Ty)
.

Inductive Statement :=
  Assign(lhs: PlaceExpr)(rhs: Rvalue)
| StorageLive(local: Local)
| StorageDead(local: Local)
| Nop
.

Definition BasicBlock := string.

Record CallData := {
    func: Operand;
    args: list Operand;
    destination: PlaceExpr;
    target: option BasicBlock;
}.

Inductive Terminator :=
| Goto(target: BasicBlock)
| SwitchInt(discr: Operand)(values: list N)(targets: list BasicBlock)
| Return
| Unreachable
| Call(call: CallData)
.

Record BasicBlockData := {
    statements: list Statement;
    terminator: Terminator;
}.

Record Body := {
    inputs: list Ty;
    output: Ty;
    local_decls: list (Local * LocalDecl);
    basic_blocks: list (BasicBlock * BasicBlockData);
}.
