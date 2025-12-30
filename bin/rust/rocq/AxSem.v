From iris.base_logic Require Export iprop.
Require Export VfMir Values.

Definition Program := list (string * Body).
Definition Env := string → Ty * Ptr.

Section gfunctors.

Context {Σ: gFunctors}.

Definition points_to(ty: Ty)(ptr: Value)(rhs: Value): iProp Σ.
Admitted.

Definition points_to_(ty: Ty)(ptr: Value)(rhs: Value): iProp Σ.
Admitted.

Lemma points_to_def(ty: Ty)(ptr: Value)(rhs: Value):
  points_to_ ty ptr (VSome rhs) ∗-∗ points_to ty ptr rhs.
Admitted.

(* [points_to_ ty ptr val] does *NOT* imply [∃ p, ptr = VPtr p]! *)
Lemma points_to__Tuple0(ptr: Value):
  ⊢ ∃ v0, points_to_ Tuple0 ptr v0.
Admitted.

Definition wp_PlaceExprElem(ptr: Value)(ty: Ty)(place_expr_elem: PlaceExprElem)(Q: Value -> Ty -> iProp Σ): iProp Σ.
Admitted.

Lemma wp_Deref_intro ptr ty ptr' (Q: Value -> Ty -> iProp Σ):
  points_to ty ptr ptr' ∗ (points_to ty ptr ptr' -∗ ∃ pointee_ty, ⌜ ty = RawPtr pointee_ty ⌝ ∗ Q ptr' pointee_ty) -∗
  wp_PlaceExprElem ptr ty Deref Q.
Admitted.

Fixpoint wp_PlaceExprElems ptr ty place_expr_elems Q :=
  match place_expr_elems with
    [] => Q ptr ty
  | place_expr_elem::place_expr_elems =>
    wp_PlaceExprElem ptr ty place_expr_elem (fun ptr ty =>
      wp_PlaceExprElems ptr ty place_expr_elems Q)
  end.

Definition wp_PlaceExpr(env: Env)(place_expr: PlaceExpr)(Q: Value -> Ty -> iProp Σ): iProp Σ :=
  let '(x, place_expr_elems) := place_expr in
  let '(ty, ptr) := env x in
  wp_PlaceExprElems (VPtr ptr) ty place_expr_elems Q.

Definition wp_Operand(env: Env)(operand: Operand)(Q: Value -> Ty -> iProp Σ): iProp Σ.
Admitted.

Lemma wp_Move_intro(env: Env)(place_expr: PlaceExpr)(Q: Value -> Ty -> iProp Σ):
  wp_PlaceExpr env place_expr (fun ptr ty =>
    ∃ v, points_to ty ptr v ∗ (points_to ty ptr v -∗ Q v ty))
  -∗ wp_Operand env (Move place_expr) Q.
Admitted.

Lemma wp_Copy_intro(env: Env)(place_expr: PlaceExpr)(Q: Value -> Ty -> iProp Σ):
  wp_PlaceExpr env place_expr (fun ptr ty =>
    ∃ v, points_to ty ptr v ∗ (points_to ty ptr v -∗ Q v ty))
  -∗ wp_Operand env (Copy place_expr) Q.
Admitted.

Lemma wp_Constant_Tuple0_intro(env: Env)(Q: Value -> Ty -> iProp Σ):
  Q VTuple0 Tuple0 -∗ wp_Operand env (Constant (Val ZeroSized Tuple0)) Q.
Admitted.

Definition wp_Rvalue(env: Env)(rvalue: Rvalue)(Q: Value -> Ty -> iProp Σ): iProp Σ.
Admitted.

Lemma wp_Use_intro(env: Env)(operand: Operand)(Q: Value -> Ty -> iProp Σ):
  wp_Operand env operand Q -∗ wp_Rvalue env (Use operand) Q.
Admitted.

Lemma wp_RawPtr__intro(env: Env)(place_expr: PlaceExpr)(Q: Value -> Ty -> iProp Σ):
  wp_PlaceExpr env place_expr (λ ptr ty, Q ptr (RawPtr ty))
  -∗ wp_Rvalue env (RawPtr_ place_expr) Q.
Admitted.

Lemma wp_Cast_PtrToPtr_intro(env: Env)(operand: Operand)(ty: Ty)(Q: Value -> Ty -> iProp Σ):
  wp_Operand env operand (fun v _ => Q v ty) -∗ wp_Rvalue env (Cast PtrToPtr operand ty) Q. (* We don't support wide pointers yet. *)
Admitted.

Definition wp_Statement(env: Env)(statement: Statement)(Q: iProp Σ): iProp Σ.
Admitted.

Lemma wp_Assign_intro(env: Env)(lhs: PlaceExpr)(rhs: Rvalue)(Q: iProp Σ):
  wp_Rvalue env rhs (fun v ty =>
    wp_PlaceExpr env lhs (fun ptr ty' =>
      (∃ state0, points_to_ ty' ptr state0) ∗ (points_to ty' ptr v -∗ Q)))
  -∗ wp_Statement env (Assign lhs rhs) Q.
Admitted.

Lemma wp_StorageLive_intro_UNSOUND(env: Env)(x: Local)(Q: iProp Σ): (* SOUNDNESS BUG: Ignored for now. https://github.com/verifast/verifast/issues/948 *)
  Q -∗ wp_Statement env (StorageLive x) Q.
Admitted.

Lemma wp_StorageDead_intro_UNSOUND(env: Env)(x: Local)(Q: iProp Σ): (* SOUNDNESS BUG: Ignored for now. https://github.com/verifast/verifast/issues/948 *)
  Q -∗ wp_Statement env (StorageDead x) Q.
Admitted.

Lemma wp_Nop_intro(env: Env)(Q: iProp Σ):
  Q -∗ wp_Statement env Nop Q.
Admitted.

Fixpoint wp_Statements(env: Env)(statements: list Statement)(Q: iProp Σ): iProp Σ :=
  match statements with
    [] => Q
  | statement::statements =>
    wp_Statement env statement (wp_Statements env statements Q)
  end.

Definition BasicBlocks := gmap string BasicBlockData.

Definition wp_Terminator
    (env: Env)(terminator: Terminator)
    (wp_call: string -> list GenericArg -> list Value -> (Value -> iProp Σ) -> iProp Σ)
    (Qbasic_block: BasicBlock -> iProp Σ)
    (Qreturn: iProp Σ)
    : iProp Σ.
Admitted.

Lemma wp_Goto_intro
    (env: Env)(bb: BasicBlock)
    (wp_call: string -> list GenericArg -> list Value -> (Value -> iProp Σ) -> iProp Σ)
    (Qbasic_block: BasicBlock -> iProp Σ)
    (Qreturn: iProp Σ):
  ▷ Qbasic_block bb -∗ wp_Terminator env (Goto bb) wp_call Qbasic_block Qreturn.
Admitted.

Definition wp_SwitchInt
    (discr: Value)(ty: Ty)(values: list N)(targets: list BasicBlock)
    (Qbasic_block: BasicBlock -> iProp Σ)
    : iProp Σ.
Admitted.

Parameter value_eqb_N: forall (ty: Ty)(value: Value)(n: N), option bool.

Axiom value_eqb_N_Bool_0_eq_true: forall v, value_eqb_N Bool v 0 = Some true → v ≠ VBool true.
Axiom value_eqb_N_Bool_1_eq_true: forall v, value_eqb_N Bool v 1 = Some true → v = VBool true.

Axiom value_eqb_N_Bool_0_eq_false: forall v, value_eqb_N Bool v 0 = Some false → v = VBool true.
Axiom value_eqb_N_Bool_1_eq_false: forall v, value_eqb_N Bool v 1 = Some false → v ≠ VBool true.

Lemma wp_SwitchInt_compare
    (discr: Value)(ty: Ty)(value: N)(values: list N)(target: BasicBlock)(targets: list BasicBlock)
    (Qbasic_block: BasicBlock → iProp Σ):
  match value_eqb_N ty discr value with
    None => True
  | Some true =>
    ▷ Qbasic_block target
  | Some false =>
    wp_SwitchInt discr ty values targets Qbasic_block
  end -∗
  wp_SwitchInt discr ty (value::values) (target::targets) Qbasic_block.
Admitted.

Lemma wp_SwitchInt_default
    (discr: Value)(ty: Ty)(target: BasicBlock)
    (Qbasic_block: BasicBlock → iProp Σ):
  ▷ Qbasic_block target
  -∗ wp_SwitchInt discr ty [] [target] Qbasic_block.
Admitted.

Lemma wp_SwitchInt_intro
    (env: Env)(discr: Operand)(values: list N)(targets: list BasicBlock)
    (wp_call: string -> list GenericArg -> list Value -> (Value -> iProp Σ) -> iProp Σ)
    (Qbasic_block: BasicBlock -> iProp Σ)
    (Qreturn: iProp Σ):
  wp_Operand env discr (fun discr ty => wp_SwitchInt discr ty values targets Qbasic_block) -∗
  wp_Terminator env (SwitchInt discr values targets) wp_call Qbasic_block Qreturn.
Admitted.

Lemma wp_Return_intro
    (env: Env)
    (wp_call: string -> list GenericArg -> list Value -> (Value -> iProp Σ) -> iProp Σ)
    (Qbasic_block: BasicBlock -> iProp Σ)
    (Qreturn: iProp Σ):
  Qreturn -∗ wp_Terminator env Return wp_call Qbasic_block Qreturn.
Admitted.

Fixpoint wp_Operands(env: Env)(operands: list Operand)(Q: list Value -> iProp Σ): iProp Σ :=
  match operands with
    [] => Q []
  | operand::operands =>
    wp_Operand env operand (fun v ty =>
      wp_Operands env operands (fun vs =>
        Q (v::vs)))
  end.

Lemma wp_ghost_command_intro env targs args destination target wp_call Qbasic_block Qreturn:
  ▷ Qbasic_block target -∗
  wp_Terminator env (Call {|
    func := Constant (Val ZeroSized (FnDef "VeriFast_ghost_command" targs));
    args := args;
    destination := destination;
    target := Some target
  |}) wp_call Qbasic_block Qreturn.
Admitted.

Lemma wp_Call_intro
    (env: Env)
    (func_name: string)(targs: GenericArgList)
    (args: list Operand)(destination: PlaceExpr)(target: option BasicBlock)
    (wp_call: string -> list GenericArg -> list Value -> (Value -> iProp Σ) -> iProp Σ)
    (Qbasic_block: BasicBlock -> iProp Σ)
    (Qreturn: iProp Σ):
  wp_Operands env args (fun args =>
    ▷ wp_call func_name (list_of_GenericArgList targs) args (fun result =>
      wp_PlaceExpr env destination (fun ptr ty =>
        ∃ state0, points_to_ ty ptr state0 ∗ (points_to ty ptr result -∗
          match target with
            None => ⌜ False ⌝
          | Some basic_block => ▷ Qbasic_block basic_block
          end))))
  -∗ wp_Terminator env (Call {|
       func := Constant (Val ZeroSized (FnDef func_name targs));
       args := args; destination := destination; target := target
     |}) wp_call Qbasic_block Qreturn.
Admitted.

Definition wp_BasicBlock
    (env: Env)(basic_block: BasicBlockData)
    (wp_call: string -> list GenericArg -> list Value -> (Value -> iProp Σ) -> iProp Σ)
    (Qbasic_block: BasicBlock -> iProp Σ)
    (Qreturn: iProp Σ): iProp Σ :=
  wp_Statements env (statements basic_block)
    (wp_Terminator env (terminator basic_block) wp_call Qbasic_block Qreturn).

Definition wp_BasicBlocks
    (env: Env)(basic_blocks: list (BasicBlock * BasicBlockData))(basic_block: BasicBlock)
    (wp_call: string -> list GenericArg -> list Value -> (Value -> iProp Σ) -> iProp Σ)
    (Qreturn: iProp Σ): iProp Σ.
Admitted. (* To be defined by guarded recursion; involves proving that wp_BasicBlock is contractive in Qbasic_block. *)

Lemma wp_BasicBlocks_intro
    (env: Env)(basic_blocks: list (BasicBlock * BasicBlockData))(basic_block: BasicBlock)
    (wp_call: string -> list GenericArg -> list Value -> (Value -> iProp Σ) -> iProp Σ)
    (Qreturn: iProp Σ):
  match assoc basic_block basic_blocks with
    None => False
  | Some basic_block_data =>
    wp_BasicBlock env basic_block_data wp_call
      (fun bb => wp_BasicBlocks env basic_blocks bb wp_call Qreturn)
      Qreturn
  end
  -∗ wp_BasicBlocks env basic_blocks basic_block wp_call Qreturn.
Admitted.

Definition wp_Body
    (body: Body)(args: list Value)
    (wp_call: string -> list GenericArg -> list Value -> (Value -> iProp Σ) -> iProp Σ)
    (Q: Value -> iProp Σ)
    : iProp Σ :=
  ∀ (env: Env),
  ⌜ ∀ x info, assoc x (local_decls body) = Some info → ∃ ptr, env x = (ty info, ptr) ⌝ -∗
  match local_decls body with
    [] => False
  | result_var_decl::local_decls' =>
    let '(param_env, (local_decls'', _)) := combine_ local_decls' args in
    ([∗ list] '((x, {| ty := ty |}), v) ∈ param_env, points_to ty (VPtr (snd (env x))) v) -∗
    ([∗ list] '(x, {| ty := ty |}) ∈ result_var_decl::local_decls'', ∃ state0, points_to_ ty (VPtr (snd (env x))) state0) -∗
    match basic_blocks body with
      (bb0, _)::_ =>
      wp_BasicBlocks env (basic_blocks body) bb0 wp_call
        (let '(result_var, {| ty := ty |}) := result_var_decl in
         ∃ result,
         points_to ty (VPtr (snd (env result_var))) result
         ∗ ([∗ list] '(x, {| ty := ty |}) ∈ local_decls', ∃ state, points_to_ ty (VPtr (snd (env x))) state)
         ∗ Q result)
    | _ => False
    end
  end.

Definition wp_call_std
    (wp_call: string -> list GenericArg -> list Value -> (Value -> iProp Σ) -> iProp Σ)
    (func_name: string)(targs: list GenericArg)(args: list Value)
    (Q: Value -> iProp Σ)
    : iProp Σ :=
  if string_dec func_name "std::ptr::mut_ptr::<impl *mut T>::is_null" then
    match args with
      [ptr] => Q (VBool (value_eqb ptr (VPtr null_ptr)))
    | _ => False%I
    end
  else if string_dec func_name "std::ptr::null_mut" then
    Q (VPtr null_ptr)
  else if string_dec func_name "std::process::abort" then
    True%I
  else
    wp_call func_name targs args Q.

Definition wp_Bodies
    (program: Program)
    (func_name: string)(targs: list GenericArg)(args: list Value)(Q: Value -> iProp Σ)
    : iProp Σ.
Admitted. (* To be defined using guarded recursion, exploiting the contractiveness of wp_Body in wp_call *)

Lemma wp_Bodies_intro
    (program: Program)
    (func_name: string)(targs: list GenericArg)(args: list Value)(Q: Value -> iProp Σ):
  match assoc func_name program with
    None => False
  | Some body =>
    wp_Body body args (wp_call_std (wp_Bodies program)) Q
  end -∗
  wp_Bodies program func_name targs args Q.
Admitted.

Definition program_has_no_ub(program: Program): Prop :=
  ⊢ wp_Bodies program "main" [] [] (fun _ => True).

End gfunctors.
