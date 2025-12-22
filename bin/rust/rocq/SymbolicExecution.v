Require Export Annotations Values.
From Coq Require Export ClassicalDescription.

Open Scope annot_scope.

Notation "f @@ x" := (f x)
  (at level 20, right associativity, only parsing).

Fixpoint remove1_assoc{T}(x: string)(xys: list (string * T)): option (T * list (string * T)) :=
  match xys with
    [] => None
  | (x', y')::xys =>
    if string_dec x' x then
      Some (y', xys)
    else
      match remove1_assoc x xys with
        None => None
      | Some (y, xys) =>
        Some (y, (x', y')::xys)
      end
  end.

Fixpoint assoc_{A B}(eq_dec: forall (x1 x2: A), {x1 = x2} + {x1 <> x2})(x: A)(xys: list (A * B)): option B :=
  match xys with
    [] => None
  | (x', y)::xys =>
    if eq_dec x x' then
      Some y
    else
      assoc_ eq_dec x xys
  end.

Fixpoint nth__iter{T}(k: nat)(xs_done: list T)(xs_todo: list T): option (T * list T) :=
  match k, xs_todo with
    O, x::xs_todo => Some (x, (xs_done ++ xs_todo)%list)
  | S k, x::xs_todo => nth__iter k (x::xs_done) xs_todo
  | _, _ => None
  end.

Definition nth_{T}(k: nat)(xs: list T): option (T * list T) :=
  nth__iter k [] xs.

Definition ProofObligation_eq_dec(o1 o2: ProofObligation): {o1 = o2} + {o1 <> o2}.
decide equality.
apply string_dec.
Defined.

Fixpoint Ty_eq_dec(ty1 ty2: Ty) {struct ty1}: {ty1 = ty2} + {ty1 <> ty2}
with GenericArg_eq_dec(arg1 arg2: GenericArg) {struct arg1}: {arg1 = arg2} + {arg1 <> arg2}
with GenericArgList_eq_dec(args1 args2: GenericArgList) {struct args1}: {args1 = args2} + {args1 <> args2}.
- decide equality.
  + decide equality.
  + decide equality.
  + apply string_dec.
- decide equality.
- decide equality.
Defined.

Inductive LocalState :=
| LSValue(v: option Value)
| LSPlace(a: Ptr) (* The environment records (a pointer to) the place where this local variable's value is stored, not the value itself *)
.

Definition Env := list (Local * LocalState).

Inductive TraceElem :=
| VerifyingBody(name: string)
| VerifyingBasicBlock(name: string)
| VerifyingStatement(index: nat)
| VerifyingTerminator
| FirstBranch
| SecondBranch
| Msg(msg: string)
.

Definition Trace := list TraceElem.

Definition Error(trace: Trace)(msg: string){T}(info: T) := False.

Definition forall_ty(trace: Trace)(ty: Ty)(Q: Value -> Prop): Prop :=
  match ty with
    RawPtr _ => forall (ptr: Ptr), Q (VPtr ptr)
  | Bool => forall (b: bool), Q (VBool b)
  | _ => Error trace "forall_ty: unsupported type" ty
  end.

Definition havoc(trace: Trace)(x: string)(ty: Ty)(env: Env)(Q: Env -> Value -> Prop): Prop :=
  forall_ty trace ty @@ fun v => Q ((x, LSValue (Some v))::env) v.

Fixpoint havoc_vars(trace: Trace)(vars: list (string * Ty))(env: Env)(Q: Env -> Prop): Prop :=
  match vars with
    [] => Q env
  | (x, ty)::vars => havoc trace x ty env (fun env _ => havoc_vars trace vars env Q)
  end.

Inductive PrimChunk :=
| PointsTo_(ty: Ty)(ptr: Value)(rhs: Value)
.

Inductive Chunk :=
| Prim(chunk: PrimChunk)
| PointsTo(ty: Ty)(ptr: Value)(rhs: Value)
| User(pred_name: string)(args: list Value)
.

Definition Heap := list Chunk.

Fixpoint eval(env: Env)(e: Expr): Value :=
  match e with
    BoolLit b => VBool b
  | RealLit q => VReal q
  | NullPtr => VPtr null_ptr
  | Var x =>
    match assoc x env with
      Some (LSValue (Some v)) => v
    | Some (LSPlace ptr) => VPtr ptr
    | _ => VDummy
    end
  | Eq e1 e2 => VBool (value_eqb (eval env e1) (eval env e2))
  end.

Definition assume(env: Env)(e: Expr)(Q: Prop): Prop :=
  match e with
    BoolLit true => Q
  | BoolLit false => True
  | e => eval env e = VBool true -> Q
  end.

Definition assume_false(env: Env)(e: Expr)(Q: Prop): Prop :=
  match e with
    BoolLit true => True
  | BoolLit false => Q
  | e => eval env e <> VBool true -> Q
  end.

Definition assert(trace: Trace)(env: Env)(e: Expr)(Q: Prop): Prop :=
  match e with
    BoolLit true => Q
  | BoolLit false => Error trace "assert: BoolLit false" tt
  | e => eval env e = VBool true /\ Q
  end.

Definition produce_pat(trace: Trace)(env: Env)(ty: Ty)(pat: Pat)(Q: Env -> Value -> Prop): Prop :=
  match pat with
    LitPat e => Q env (eval env e)
  | VarPat x => forall v, Q ((x, LSValue (Some v))::env) v
  end.

Fixpoint produce_pats(trace: Trace)(env: Env)(pats: list Pat)(Q: Env -> list Value -> Prop): Prop :=
  match pats with
    [] => Q env []
  | pat::pats =>
    match pat with
      LitPat e =>
      let v := eval env e in
      produce_pats trace env pats @@ fun env vs => Q env (v::vs)
    | _ => Error trace "produce_pats: unsupported pattern" pat
    end
  end.

Fixpoint produce(trace: Trace)(h: Heap)(env: Env)(tree: SymexTree)(a: Asn)(Q: Heap -> Env -> SymexTree -> Prop): Prop :=
  match a with
    BoolAsn e => assume env e @@ Q h env tree
  | PointsToAsn ty ptr rhs =>
    let ptr := eval env ptr in
    produce_pat trace env ty rhs @@ fun env vrhs =>
    Q (PointsTo ty ptr vrhs::h) env tree
  | PredAsn name args =>
    produce_pats trace env args @@ fun env vs =>
    Q (User name vs::h) env tree
  | SepAsn a1 a2 =>
    produce trace h env tree a1 @@ fun h env tree =>
    produce trace h env tree a2 Q
  | IfAsn e a1 a2 =>
    match tree with
      Fork tree1 tree2 =>
      assume env e @@ produce (FirstBranch::trace) h env tree1 a1 Q /\
      assume_false env e @@ produce (SecondBranch::trace) h env tree2 a2 Q
    | _ => Error trace "produce: IfAsn: bad tree: Fork expected" tree
    end
  end.

Definition match_pat(env: Env)(pat: Pat)(v: Value)(Q: Env -> Prop): Prop :=
  match pat with
    LitPat e => v = eval env e /\ Q env
  | VarPat x => Q ((x, LSValue (Some v))::env)
  end.

Fixpoint match_pats(trace: Trace)(env: Env)(pats: list Pat)(vs: list Value)(Q: Env -> Prop): Prop :=
  match pats, vs with
    [], [] => Q env
  | pat::pats, v::vs =>
    match_pat env pat v @@ fun env =>
    match_pats trace env pats vs Q
  | _, _ => Error trace "match_pats: length mismatch" (pats, vs)
  end.

Fixpoint consume_chunk(trace: Trace)(h: Heap)(tree: SymexTree)(Q: Heap -> SymexTree -> Chunk -> Prop): Prop :=
  match tree with
    AutoOpen k;; tree =>
    match nth_ k h with
      None => Error trace "consume_chunk: AutoOpen: bad heap index" (k, h)
    | Some (chunk, h) =>
      match chunk with
        PointsTo ty ptr v =>
        let h := Prim (PointsTo_ ty ptr (VSome v))::h in
        consume_chunk trace h tree Q
      | _ => Error trace "consume_chunk: AutoOpen: bad chunk" chunk
      end
    end
  | ConsumeChunk k;; tree =>
    match nth_ k h with
      None => Error trace "consume_chunk: ConsumeChunk: bad heap index" (k, h)
    | Some (chunk, h) =>
      Q h tree chunk
    end
  | _ => Error trace "consume_chunk: bad tree" tree
  end.

Definition consume_points_to(trace: Trace)(h: Heap)(tree: SymexTree)(ty: Ty)(ptr: Value)(Q: Heap -> SymexTree -> Value -> Prop): Prop :=
  consume_chunk trace h tree @@ fun h tree chunk =>
  match chunk with
    PointsTo ty' ptr' v =>
    ty' = ty /\
    ptr' = ptr /\
    Q h tree v
  | _ => Error trace "consume_points_to: bad chunk" chunk
  end.

Definition consume_points_to_(trace: Trace)(h: Heap)(tree: SymexTree)(ty: Ty)(ptr: Value)(Q: Heap -> SymexTree -> Value -> Prop): Prop :=
  consume_chunk trace h tree @@ fun h tree chunk =>
  match chunk with
    Prim (PointsTo_ ty' ptr' v) =>
    ty' = ty /\
    ptr' = ptr /\
    Q h tree v
  | _ => Error trace "consume_points_to_: bad chunk" chunk
  end.

Fixpoint consume(trace: Trace)(h: Heap)(env: Env)(tree: SymexTree)(a: Asn)(Q: Heap -> Env -> SymexTree -> Prop): Prop :=
  match a with
    BoolAsn e => assert trace env e @@ Q h env tree
  | PointsToAsn ty ptr rhs =>
    consume_points_to trace h tree ty (eval env ptr) @@ fun h tree v =>
    match_pat env rhs v @@ fun env =>
    Q h env tree
  | PredAsn name pats =>
    consume_chunk trace h tree @@ fun h tree chunk =>
    match chunk with
      User name' args =>
      name = name' /\
      match_pats trace env pats args @@ fun env =>
      Q h env tree
    | _ => Error trace "consume: PredAsn: bad chunk" chunk
    end
  | SepAsn a1 a2 =>
    consume trace h env tree a1 @@ fun h env tree =>
    consume trace h env tree a2 Q
  | IfAsn e a1 a2 =>
    match tree with
      Fork tree1 tree2 =>
      assume env e @@ consume (FirstBranch::trace) h env tree1 a1 Q /\
      assume_false env e @@ consume (SecondBranch::trace) h env tree2 a2 Q
    | _ => Error trace "consume: bad tree" tree
    end
  end.

Section Specs.

Variable preds: list (string * PredDef).
Variable specs: list (string * Spec).
Variable trees: list (ProofObligation * SymexTree).

Fixpoint process_param_addr_taken_steps(trace: Trace)(h: Heap)(env: Env)(tree: SymexTree)(Q: Heap -> Env -> SymexTree -> Prop): Prop :=
  match tree with
    ParamAddrTaken x true;; tree => Error trace "process_param_addr_taken_steps: ParamAddrTaken true is not yet supported" tree
  | ParamAddrTaken x false;; tree => process_param_addr_taken_steps trace h env tree Q
  | tree => Q h env tree
  end.

Fixpoint process_local_addr_taken_steps(trace: Trace)(h: Heap)(env: Env)(tree: SymexTree)(local_decls: list (Local * LocalDecl))
    (Q: Heap -> Env -> SymexTree -> forall (dealloc_heapy_locals: Heap -> SymexTree -> (Heap -> SymexTree -> Prop) -> Prop), Prop)
    : Prop :=
  match local_decls with
    [] => Q h env tree (fun h tree Q => Q h tree)
  | (x, {| ty := ty |})::local_decls =>
    match tree with
      LocalAddrTaken x' b;; tree =>
      if string_dec x x' then
        if b then
          forall ptr value,
          ptr <> null_ptr ->
          let '(h, cleanup_heapy_locals) :=
            match ty with
              Never | Tuple0 => (h, (fun cleanup_heapy_locals' => cleanup_heapy_locals'))
            | _ =>
              (Prim (PointsTo_ ty (VPtr ptr) value)::h,
               (fun cleanup_heapy_locals' h tree Q =>
                consume_points_to_ trace h tree ty (VPtr ptr) @@ fun h tree _ =>
                cleanup_heapy_locals' h tree Q))
            end
          in
          let env := ((x, LSPlace ptr)::env) in
          process_local_addr_taken_steps trace h env tree local_decls @@ fun h env tree cleanup_heapy_locals' =>
          Q h env tree (cleanup_heapy_locals cleanup_heapy_locals')
        else
          let env := ((x, LSValue None)::env) in
          process_local_addr_taken_steps trace h env tree local_decls Q
      else
        Error trace "process_local_addr_taken_steps: local variable name does not match" tree
    | _ => Error trace "process_local_addr_taken_steps: bad tree: LocalAddrTaken expected" tree
    end
  end.

Section LocalDecls.

Variable local_decls: list (Local * LocalDecl).

Definition load_from_pointer(trace: Trace)(h: Heap)(tree: SymexTree)(ty: Ty)(ptr: Value)(Q: Heap -> SymexTree -> Value -> Prop): Prop :=
  consume_points_to trace h tree ty ptr @@ fun h tree v =>
  let h := PointsTo ty ptr v::h in
  Q h tree v.

Inductive Place :=
  PNonAddrTakenLocal(x: Local)
| PDeref(ptr: Value)
.

Definition load_from_place(trace: Trace)(h: Heap)(env: Env)(tree: SymexTree)(place: Place)(ty: Ty)(Q: Heap -> SymexTree -> Value -> Prop): Prop :=
  match place with
    PNonAddrTakenLocal x =>
    match assoc x env with
      Some (LSValue (Some v)) => Q h tree v
    | _ => Error trace "load_from_place: dangling local" (x, env)
    end
  | PDeref ptr =>
    load_from_pointer trace h tree ty ptr @@ fun h tree v =>
    Q h tree v
  end.

Definition store_to_place(trace: Trace)(h: Heap)(env: Env)(tree: SymexTree)(place: Place)(ty: Ty)(v: Value)(Q: Heap -> Env -> SymexTree -> Prop): Prop :=
  if Ty_eq_dec ty Tuple0 then
    Q h env tree
  else
    match place with
      PNonAddrTakenLocal x =>
      match remove1_assoc x env with
      | Some (LSValue _, xys) =>
        let env := (x, LSValue (Some v))::xys in
        Q h env tree
      | _ => Error trace "store_to_place: no such local" (x, env)
      end
    | PDeref ptr =>
      consume_points_to_ trace h tree ty ptr @@ fun h tree _ =>
      let h := PointsTo ty ptr v::h in
      Q h env tree
    end.

Definition verify_local(trace: Trace)(env: Env)(x: Local)(Q: Place -> Ty -> Prop): Prop :=
  match assoc x local_decls with
    Some {| ty := ty |} =>
    match assoc x env with
      Some (LSValue _) => Q (PNonAddrTakenLocal x) ty
    | Some (LSPlace ptr) => Q (PDeref (VPtr ptr)) ty
    | None => Error trace "verify_local: dangling local" (x, env)
    end
  | None => Error trace "verify_local: no such local" x
  end.

Definition verify_place_expr_elem
    (trace: Trace)
    (h: Heap)(env: Env)(tree: SymexTree)(place: Place)(ty: Ty)(place_expr_elem: PlaceExprElem)
    (Q: Heap -> SymexTree -> Place -> Ty -> Prop)
    : Prop :=
  match place_expr_elem with
  | Deref =>
    load_from_place trace h env tree place ty @@ fun h tree v =>
    match ty with
      RawPtr ty => Q h tree (PDeref v) ty
    | _ => Error trace "verify_place_expr_elem: Deref: bad place type: must match RawPtr _" ty
    end
  end.

Fixpoint verify_place_expr_elems
    (trace: Trace)
    (h: Heap)(env: Env)(tree: SymexTree)(place: Place)(ty: Ty)(place_expr_elems: list PlaceExprElem)
    (Q: Heap -> SymexTree -> Place -> Ty -> Prop)
    {struct place_expr_elems}
    : Prop :=
  match place_expr_elems with
    [] => Q h tree place ty
  | place_expr_elem::place_expr_elems =>
    verify_place_expr_elem trace h env tree place ty place_expr_elem @@ fun h tree place ty =>
    verify_place_expr_elems trace h env tree place ty place_expr_elems Q
  end.

Definition verify_place_expr(trace: Trace)(h: Heap)(env: Env)(tree: SymexTree)(place_expr: PlaceExpr)(Q: Heap -> SymexTree -> Place -> Ty -> Prop): Prop :=
  let '(x, place_expr_elems) := place_expr in
  verify_local trace env x @@ fun place ty =>
  verify_place_expr_elems trace h env tree place ty place_expr_elems Q.

Definition verify_operand(trace: Trace)(h: Heap)(env: Env)(tree: SymexTree)(operand: Operand)(Q: Heap -> SymexTree -> Value -> Ty -> Prop): Prop :=
  match operand with
    Move place_expr =>
    verify_place_expr trace h env tree place_expr @@ fun h tree place ty =>
    load_from_place trace h env tree place ty @@ fun h tree v =>
    Q h tree v ty
  | Copy place_expr =>
    verify_place_expr trace h env tree place_expr @@ fun h tree place ty =>
    load_from_place trace h env tree place ty @@ fun h tree v =>
    Q h tree v ty
  | Constant (Val ZeroSized Tuple0) =>
    Q h tree VTuple0 Tuple0
  | _ => Error trace "verify_operand: unsupported operand" operand
  end.

Fixpoint verify_operands
    (trace: Trace)(h: Heap)(env: Env)(tree: SymexTree)(operands: list Operand)
    (Q: Heap -> SymexTree -> list Value -> Prop)
    : Prop :=
  match operands with
    [] => Q h tree []
  | operand::operands =>
    verify_operand trace h env tree operand @@ fun h tree v ty =>
    verify_operands trace h env tree operands @@ fun h tree vs =>
    Q h tree (v::vs)
  end.

Definition verify_rvalue(trace: Trace)(h: Heap)(env: Env)(tree: SymexTree)(rvalue: Rvalue)(Q: Heap -> SymexTree -> Value -> Ty -> Prop): Prop :=
  match rvalue with
    Use operand =>
    verify_operand trace h env tree operand Q
  | RawPtr_ place_expr =>
    verify_place_expr trace h env tree place_expr @@ fun h tree place ty =>
    match place with
      PNonAddrTakenLocal _ => Error trace "verify_rvalue: RawPtr_: place must not be PNonAddrTakenLocal" place
    | PDeref ptr => Q h tree ptr (RawPtr ty)
    end
  | Cast PtrToPtr operand ty =>
    verify_operand trace h env tree operand @@ fun h tree v ty0 =>
    Q h tree v ty (* We do not support wide pointers yet, so this does not change the value *)
  | _ => Error trace "verify_rvalue: unsupported rvalue" rvalue
  end.

Definition verify_statement(trace: Trace)(h: Heap)(env: Env)(tree: SymexTree)(statement: Statement)(Q: Heap -> Env -> SymexTree -> Prop): Prop :=
  match statement with
  | Assign lhs rhs =>
    verify_rvalue trace h env tree rhs @@ fun h tree v ty_rhs =>
    verify_place_expr trace h env tree lhs @@ fun h tree place ty => (* SOUNDNESS: Is it okay to evaluate the RHS before the LHS? *)
    store_to_place trace h env tree place ty v Q
  | StorageLive x => Q h env tree (* SOUNDNESS BUG: Ignored for now. https://github.com/verifast/verifast/issues/948 *)
  | StorageDead x => Q h env tree (* SOUNDNESS BUG: Ignored for now. https://github.com/verifast/verifast/issues/948 *)
  | Nop => Q h env tree
  end.

Fixpoint verify_statements(trace: Trace)(h: Heap)(env: Env)(tree: SymexTree)(statements: list Statement)(Q: Heap -> Env -> SymexTree -> Prop): Prop :=
  match statements with
    [] => Q h env tree
  | s::ss =>
    verify_statement trace h env tree s @@ fun h env tree =>
    verify_statements trace h env tree ss Q
  end.

Definition assume_value_eq_N(trace: Trace)(v: Value)(ty: Ty)(value: N)(Q: Prop): Prop :=
  match value, ty with
    0%N, Bool => v <> VBool true -> Q
  | 1%N, Bool => v = VBool true -> Q
  | _, _ => Error trace "assume_value_eq_N: unsupported type" ty
  end.

Definition assume_value_neq_N(trace: Trace)(v: Value)(ty: Ty)(value: N)(Q: Prop): Prop :=
  match value, ty with
    0%N, Bool => v = VBool true -> Q
  | 1%N, Bool => v <> VBool true -> Q
  | _, _ => Error trace "assume_value_neq_N: unsupported type" ty
  end.

Fixpoint verify_switch_int
    (trace: Trace)(h: Heap)(env: Env)(tree: SymexTree)(v: Value)(ty: Ty)(values: list N)(targets: list BasicBlock)
    (Qbb: Heap -> Env -> SymexTree -> BasicBlock -> Prop)
    : Prop :=
  match values, targets with
    [], [default_target] => Qbb h env tree default_target
  | value::values, target::targets =>
    match tree with
      Fork tree1 tree2 =>
      (assume_value_neq_N trace v ty value @@ verify_switch_int (SecondBranch::trace) h env tree1 v ty values targets Qbb) /\
      (assume_value_eq_N trace v ty value @@ Qbb h env tree2 target)
    | _ => Error trace "verify_switch_int: bad tree: Fork expected" tree
    end
  | _, _ => Error trace "verify_switch_int: length mismatch" (values, targets)
  end.

Definition verify_call
    (trace: Trace)(h: Heap)(tree: SymexTree)(func_name: string)(targs: GenericArgList)(args: list Value)
    (Q: Heap -> SymexTree -> Value -> Prop)
    : Prop :=
  if string_dec func_name "std::ptr::mut_ptr::<impl *mut T>::is_null" then
    match args with
      [ptr] =>
      Q h tree (VBool (value_eqb ptr (VPtr null_ptr)))
    | _ =>  Error trace "verify_call: is_null: bad args" args
    end
  else if string_dec func_name "std::ptr::null_mut" then
    Q h tree (VPtr null_ptr)
  else if string_dec func_name "std::process::abort" then
    True
  else
    match assoc func_name specs with
      None => Error trace "verify_call: callee has no spec" func_name
    | Some spec =>
      let env := combine (map fst (spec_params spec)) (map (fun v => LSValue (Some v)) args) in
      consume trace h env tree (pre spec) @@ fun h env tree =>
      forall_ty trace (spec_output spec) @@ fun result =>
      let env := ("result", LSValue (Some result))::env in
      produce trace h env tree (post spec) @@ fun h env tree =>
      Q h tree result
    end.

Fixpoint eval_pats(trace: Trace)(env: Env)(pats: list Pat)(Q: list Value -> Prop): Prop :=
  match pats with
    [] => Q []
  | LitPat e::pats =>
    let v := eval env e in
    eval_pats trace env pats @@ fun vs =>
    Q (v::vs)
  | pat::pats => Error trace "eval_pats: pattern not supported here" pat
  end.

Definition verify_ghost_command(trace: Trace)(h: Heap)(env: Env)(tree: SymexTree)(Q: Heap -> Env -> SymexTree -> Prop): Prop :=
  match tree with
    Open;; tree =>
    consume_chunk trace h tree @@ fun h tree chunk =>
    match chunk with
      User pred_name args =>
      match assoc pred_name preds with
        None => Error trace "verify_ghost_command: Open: no such predicate" pred_name
      | Some pred_def =>
        let env' := combine (map fst (params pred_def)) (map (fun v => LSValue (Some v)) args) in
        produce trace h env' tree (body pred_def) @@ fun h _ tree =>
        Q h env tree
      end
    | _ => Error trace "verify_ghost_command: Open: predicate not supported" chunk
    end
  | Close (RealLit 1%Q) pred_name [] arg_pats;; tree =>
    eval_pats trace env arg_pats @@ fun vs =>
    match assoc pred_name preds with
      None => Error trace "verify_ghost_command: Close: no such predicate" pred_name
    | Some pred_def =>
      let env' := combine (map fst (params pred_def)) (map (fun v => LSValue (Some v)) vs) in
      consume trace h env' tree (body pred_def) @@ fun h _ tree =>
      let h := User pred_name vs::h in
      Q h env tree
    end
  | _ => Error trace "verify_ghost_command: bad tree: no ghost command found" tree
  end.

Definition verify_terminator
    (trace: Trace)
    (h: Heap)(env: Env)(tree: SymexTree)(terminator: Terminator)
    (Qreturn: Heap -> Env -> SymexTree -> Prop)
    (Qbb: Heap -> Env -> SymexTree -> BasicBlock -> Prop)
    : Prop :=
  match terminator with
    Goto bb => Qbb h env tree bb
  | SwitchInt discr values targets =>
    verify_operand trace h env tree discr @@ fun h tree v ty =>
    verify_switch_int trace h env tree v ty values targets Qbb
  | Return => Qreturn h env tree
  | Unreachable => Error trace "verify_terminator: Unreachable: reached" tt
  | Call ({| func := Constant (Val ZeroSized (FnDef "VeriFast_ghost_command" GALNil)) |} as call) =>
    verify_ghost_command trace h env tree @@ fun h env tree =>
    match target call with
      None => Error trace "verify_terminator: Call: VeriFast_ghost_command: target expected" tt
    | Some bb => Qbb h env tree bb
    end
  | Call ({| func := Constant (Val ZeroSized (FnDef name targs)) |} as call) =>
    verify_operands trace h env tree (VfMir.args call) @@ fun h tree args =>
    verify_call trace h tree name targs args @@ fun h tree result =>
    verify_place_expr trace h env tree (destination call) @@ fun h tree place ty =>
    store_to_place trace h env tree place ty result @@ fun h env tree =>
    match target call with
      None => Error trace "verify_terminator: Call: target expected" tt
    | Some bb => Qbb h env tree bb
    end
  | _ => Error trace "verify_terminator: unsupported terminator" terminator
  end.

Definition verify_basic_block
    (trace: Trace)
    (h: Heap)(env: Env)(tree: SymexTree)(bb: BasicBlockData)
    (Qreturn: Heap -> Env -> SymexTree -> Prop)
    (Qbb: Heap -> Env -> SymexTree -> BasicBlock -> Prop)
    : Prop :=
  verify_statements trace h env tree (statements bb) @@ fun h env tree =>
  verify_terminator trace h env tree (terminator bb) Qreturn Qbb.

Fixpoint verify_basic_blocks
    (trace: Trace)
    (basic_blocks: list (BasicBlock * BasicBlockData))
    (fuel: nat)(h: Heap)(env: Env)(tree: SymexTree)(bb: BasicBlockData)
    (Qreturn: Heap -> Env -> SymexTree -> Prop)
    : Prop :=
  match fuel with
    O => Error trace "verify_basic_blocks: Ran out of fuel" tt
  | S fuel =>
    verify_basic_block trace h env tree bb Qreturn @@ fun h env tree bb =>
    match assoc bb basic_blocks with
      None =>
      Error trace "verify_basic_blocks: no such basic block" bb
    | Some bb =>
      verify_basic_blocks trace basic_blocks fuel h env tree bb Qreturn
    end
  end.

End LocalDecls.

Definition body_is_correct(trace: Trace)(body: Body)(spec: Spec)(tree: SymexTree): Prop :=
  match local_decls body with
    [] => Error trace "body_is_correct: body has no return local" tt
  | (result_var_decl::local_decls) as all_local_decls =>
    let '(params, (local_decls, _)) := combine_ local_decls (inputs body) in
    let param_tys := map (fun '((name, _), ty) => (name, ty)) params in
    havoc_vars trace param_tys [] @@ fun env =>
    produce trace [] env tree (pre spec) @@ fun h env tree =>
    let env_after_pre := env in
    process_param_addr_taken_steps trace h env tree @@ fun h env tree =>
    process_local_addr_taken_steps trace h env tree (result_var_decl::local_decls) @@ fun h env tree cleanup_heapy_locals =>
    match basic_blocks body with
      (_, bb)::_ =>
      verify_basic_blocks all_local_decls trace (basic_blocks body) (List.length (basic_blocks body)) h env tree bb @@ fun h env tree =>
      cleanup_heapy_locals h tree @@ fun h tree =>
      match assoc (fst result_var_decl) env with
        Some (LSValue result) =>
        consume trace h (("result", LSValue result)::env_after_pre) tree (post spec) @@ fun h env tree =>
        True
      | _ => Error trace "body_is_correct: could not find return local in env" (fst result_var_decl, env)
      end
    | _ => Error trace "body_is_correct: body has no basic blocks" tt
    end
  end.

Definition named_body_is_correct(func_name: string)(body: Body): Prop :=
  let trace := [VerifyingBody func_name] in
  match assoc func_name specs with
    None => Error trace "named_body_is_correct: no spec found" tt
  | Some spec =>
    match assoc_ ProofObligation_eq_dec (Verifying func_name) trees with
      None => Error trace "named_body_is_correct: no tree found" tt
    | Some tree =>
      body_is_correct trace body spec tree
    end
  end.

Definition bodies_are_correct(bodies: list (string * Body)): Prop :=
  fold_right (fun '(func_name, body) P => named_body_is_correct func_name body /\ P) True bodies.

End Specs.
