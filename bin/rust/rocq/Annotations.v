Require Export VfMir.

From Coq Require Export QArith.

Inductive Expr :=
| BoolLit(b: bool)
| RealLit(q: Q)
| NullPtr
| Var(x: string)
| Eq(e1: Expr)(e2: Expr)
.

Inductive Pat :=
| LitPat(e: Expr)
| VarPat(x: string)
.

Inductive Asn :=
| BoolAsn(e: Expr)
| PointsToAsn(ty: Ty)(ptr: Expr)(rhs: Pat)
| PredAsn(pred_name: string)(args: list Pat)
| SepAsn(a1: Asn)(a2: Asn)
| IfAsn(cond: Expr)(if_true: Asn)(if_false: Asn)
.

Record PredDef := {
    params: list (string * Ty);
    body: Asn
}.

Record Spec := {
    spec_params: list (string * Ty);
    spec_output: Ty;
    pre: Asn;
    post: Asn;
}.

Inductive ProofObligation :=
| Verifying(func_name: string)
.

Inductive StepData :=
| ParamAddrTaken(x: string)(addr_taken: bool)
| LocalAddrTaken(x: string)(addr_taken: bool)
| Open
| ConsumeChunk(chunk_index: nat)
| AutoOpen(chunk_index: nat)
| Close(coef: Expr)(pred_name: string)(targs: list Ty)(arg_pats: list Pat)
.

Inductive SymexTree :=
| Step(data: StepData)(tree: SymexTree)
| Fork(left: SymexTree)(right: SymexTree)
| Done
.

Infix ";;" := Step (at level 60, right associativity).