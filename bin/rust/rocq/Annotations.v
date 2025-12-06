Require Export VfMir.

Inductive Expr :=
| True
| Var(x: string)
| NullPtr
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
    pred_name: string;
    params: list (string * Ty);
    body: Asn
}.
