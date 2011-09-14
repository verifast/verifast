open Verifast
open SExpressions


(*
  Utility functions
*)
let build_list (items : sexpression list) (keyword_pairs : (string * sexpression) list) =
  let build_pair (kw, sexpr) =
    [ Keyword kw; sexpr ]
  in
  List (items @ flatmap build_pair keyword_pairs)

let quote sexpr = List [ Symbol "quote"; sexpr ]

let quoted_symbol (id : string) = quote $. Symbol id

let sexpr_of_bool : bool -> sexpression = function
  | true  -> Symbol "#t"
  | false -> Symbol "#f"

let sexpr_of_int n : sexpression =
  Number (Big_int.big_int_of_int n)

let sexpr_of_option
    (if_some : 'a -> sexpression)
    ?(if_none : unit -> sexpression = fun () -> Symbol "nil")
    (opt : 'a option) =
  match opt with
    | Some x -> if_some x
    | None   -> if_none ()

let sexpr_of_list ?(head : sexpression option = None) func xs : sexpression =
  let xs = List.map func xs
  in
  match head with
    | None       -> List xs
    | Some sexpr -> List (sexpr :: xs)

(*
  Verifast-specific sexpr_of_* functions
*)
exception Unsupported of string

let unsupported_exception = ref true

let unsupported str =
  if !unsupported_exception
  then raise (Unsupported str)
  else List [ Symbol "unsupported"; Symbol str ]


let sexpr_of_ghostness (g : ghostness) : sexpression =
  let aux s = quoted_symbol s in
  match g with
    | Ghost -> aux "ghost"
    | Real  -> aux "real"

let rec sexpr_of_type_ (t : type_) : sexpression =
  let aux s = List [ Symbol s ] in
  match t with
    | Bool                    -> aux "type-bool"
    | Void                    -> aux "type-void"
    | IntType                 -> aux "type-int"
    | ShortType               -> aux "type-short"
    | UintPtrType             -> aux "type-uint-ptr"
    | RealType                -> aux "type-real"
    | Char                    -> aux "type-char"
    | StructType s            -> List [ Symbol "type-struct"; Symbol s ]
    | PtrType t               -> List [ Symbol "type-pointer-to"; sexpr_of_type_ t ]
    | FuncType s              -> List [ Symbol "type-function"; Symbol s ]
    | InductiveType (s, ts)   -> List ( Symbol "type-inductive" ::
                                        Symbol s ::
                                        List.map sexpr_of_type_ ts )
    | PredType _              -> unsupported "PredType"
    | PureFuncType _          -> unsupported "PureFuncType"
    | ObjType _               -> unsupported "ObjType"
    | ArrayType _             -> unsupported "ArrayType"
    | BoxIdType _             -> unsupported "BoxIdType"
    | HandleIdType _          -> unsupported "HandleIdType"
    | AnyType _               -> unsupported "AnyType"
    | TypeParam _             -> unsupported "TypeParam"
    | InferredType _          -> unsupported "InferredType"
    | ClassOrInterfaceName _  -> unsupported "ClassOrInterfaceName"
    | PackageName _           -> unsupported "PackageName"
    | RefType _               -> unsupported "RefType"

let rec sexpr_of_type_expr : type_expr -> sexpression = function
  | StructTypeExpr (_, name)   -> List [ Symbol "type-expr-struct"
                                       ; Symbol name ]
  | PtrTypeExpr (_, te)        -> List [ Symbol "type-expr-pointer-to"
                                       ; sexpr_of_type_expr te ]
  | ManifestTypeExpr (_, t)    -> List [ Symbol "type-expr-manifest"
                                       ; sexpr_of_type_ t ]
  | ArrayTypeExpr _            -> unsupported "ArrayTypeExpr"
  | IdentTypeExpr _            -> unsupported "IdentTypeExpr"
  | ConstructedTypeExpr _      -> unsupported "ConstructedTypeExpr"
  | PredTypeExpr _             -> unsupported "PredTypeExpr"
  | PureFuncTypeExpr _         -> unsupported "PureFuncTypeExpr"

let sexpr_of_type_expr_option : type_expr option -> sexpression = function
  | Some t -> sexpr_of_type_expr t
  | None   -> Symbol "nil"

let sexpr_of_field (Field (loc, ghostness, type_expr, name, binding, visibility, final, expr)) : sexpression =
  build_list
    [ Symbol name ]
    [ "ghostness", sexpr_of_ghostness ghostness
    ; "type", sexpr_of_type_expr type_expr ]

let sexpr_of_func_kind kind =
  let aux s = Symbol s
  in
  match kind with
    | Regular  -> aux "regular"
    | Fixpoint -> aux "fixpoint"
    | Lemma _  -> aux "lemma"

let sexpr_of_ident_scope (scope : ident_scope) : sexpression =
  match scope with
    | LocalVar           -> Symbol "local"
    | PureCtor           -> Symbol "pure-constructor"
    | FuncName           -> Symbol "function"
    | PredFamName        -> Symbol "predicate-family"
    | EnumElemName n     -> Symbol "enumeration-member"
    | GlobalName         -> Symbol "global"
    | ModuleName         -> Symbol "module"
    | PureFuncName       -> Symbol "pure-function"

let sexpr_of_operator (op : operator) : sexpression =
  match op with
    | Add         -> Symbol "+"
    | Sub         -> Symbol "-"
    | Le          -> Symbol "<="
    | Lt          -> Symbol "<"
    | Eq          -> Symbol "="
    | Neq         -> Symbol "!="
    | And         -> Symbol "&"
    | Or          -> Symbol "|"
    | Not         -> Symbol "!"
    | Mul         -> Symbol "*"
    | Div         -> Symbol "/"
    | Mod         -> Symbol "%"
    | BitNot      -> Symbol "bit-not"
    | BitAnd      -> Symbol "bit-and"
    | BitXor      -> Symbol "bit-xor"
    | BitOr       -> Symbol "bt-or"
    | ShiftLeft   -> Symbol "<<"
    | ShiftRight  -> Symbol ">>"

let sexpr_of_method_binding (binding : method_binding) : sexpression =
  match binding with
    | Static   -> Symbol "class-method"
    | Instance -> Symbol "instance-method"

let rec sexpr_of_expr (expr : expr) : sexpression =
  match expr with
    | Operation (loc, op, exprs, types) -> 
      build_list [ Symbol "expr-op"
                 ; sexpr_of_operator op ]
                 [ "operands", List (List.map sexpr_of_expr exprs)
                 ; "types",
                   match !types with
                   | Some types -> List (List.map sexpr_of_type_ types)
                   | None       -> Symbol "nil" ]
    | CallExpr (loc, name, targs, indices, args, binding) ->
      build_list [ Symbol "expr-call"
                 ; Symbol name ]
                 [ "type-arguments", List (List.map sexpr_of_type_expr targs)
                 ; "indices", List (List.map sexpr_of_pat indices)
                 ; "arguments", List (List.map sexpr_of_pat args)
                 ; "binding", sexpr_of_method_binding binding ]
    | True loc   -> Symbol "expr-true"
    | False loc  -> Symbol "expr-false"
    | Null loc   -> Symbol "expr-null"
    | Var (loc, name, scope) ->
      let scope_kw =
        match !scope with
                 | Some scope -> [ "scope", sexpr_of_ident_scope scope ]
                 | None       -> []
      in
      build_list [ Symbol "expr-var"
                 ; Symbol name ]
                 scope_kw
    | Read (loc, expr, str) ->
      List [ Symbol "expr-read"
           ; sexpr_of_expr expr
           ; Symbol str ]
    | IntLit (loc, n, t) ->
        let kw_args =
          match !t with
            | Some t -> [ "type", sexpr_of_type_ t ]
            | None   -> []
        in
        build_list [ Symbol "expr-int"
                   ; Number n ]
                   kw_args
    | AssignExpr (loc, lhs, rhs) ->
      List [ Symbol "expr-assign"
           ; sexpr_of_expr lhs
           ; sexpr_of_expr rhs ]
    | SizeofExpr (loc, texpr) ->
      List [ Symbol "expr-sizeof"
           ; sexpr_of_type_expr texpr ]
    | AssignOpExpr (loc, lhs, op, rhs, post, ts, lhs_type) ->
      build_list [ Symbol "expr-assign-op" ]
                 [ "lhs", sexpr_of_expr lhs
                 ; "rhs", sexpr_of_expr rhs
                 ; "op", sexpr_of_operator op
                 ; "post", sexpr_of_bool post ]
    | StringLit _               -> unsupported "StringLit"
    | ClassLit _                -> unsupported "ClassLit"
    | ArrayLengthExpr _         -> unsupported "ArrayLengthExpr"
    | WRead _                   -> unsupported "WRead"
    | ReadArray _               -> unsupported "ReadArray"
    | WReadArray _              -> unsupported "WReadArray"
    | Deref _                   -> unsupported "Deref"
    | ExprCallExpr _            -> unsupported "ExprCallExpr"
    | WFunPtrCall _             -> unsupported "WFunPtrCall"
    | WPureFunCall _            -> unsupported "WPureFunCall"
    | WPureFunValueCall _       -> unsupported "WPureFunValueCall"
    | WFunCall _                -> unsupported "WFunCall"
    | WMethodCall _             -> unsupported "WMethodCall"
    | NewArray _                -> unsupported "NewArray"
    | NewObject _               -> unsupported "NewObject"
    | NewArrayWithInitializer _ -> unsupported "NewArrayWithInitializer"
    | IfExpr _                  -> unsupported "IfExpr"
    | SwitchExpr _              -> unsupported "SwitchExpr"
    | PredNameExpr _            -> unsupported "PredNameExpr"
    | CastExpr _                -> unsupported "CastExpr"
    | AddressOf _               -> unsupported "AddressOf"
    | ProverTypeConversion _    -> unsupported "ProverTypeConversion"
    | ArrayTypeExpr' _          -> unsupported "ArrayTypeExpr'"
    | InstanceOfExpr _          -> unsupported "InstanceOfExpr"

and sexpr_of_pat (pat : pat) : sexpression =
  match pat with
    | LitPat expr  -> List [ Symbol "pat-literal"; sexpr_of_expr expr ]
    | VarPat str   -> List [ Symbol "pat-variable"; Symbol str ]
    | DummyPat     -> List [ Symbol "pat-dummy" ]

let rec sexpr_of_pred (pred : pred) : sexpression =
  match pred with
    | IfPred (loc, expr, thenp, elsep) ->
      List [ Symbol "pred-if"
           ; sexpr_of_expr expr
           ; sexpr_of_pred thenp
           ; sexpr_of_pred elsep ]
    | CallPred (loc, predref, types, indices, patterns) ->
      build_list [ Symbol "pred-call-predicate"
                 ; Symbol predref#name ]
                 [ "types", List (List.map sexpr_of_type_expr types)
                 ; "indices", List (List.map sexpr_of_pat indices)
                 ; "arguments", List (List.map sexpr_of_pat patterns) ]
    | Access (loc, expr, pat) ->
      List [ Symbol "pred-access"
           ; sexpr_of_expr expr
           ; sexpr_of_pat pat ]
    | EmpPred loc ->
      List [ Symbol "pred-empty" ]
    | Sep (loc, l, r) ->
      List [ Symbol "pred-&*&"
           ; sexpr_of_pred l
           ; sexpr_of_pred r ]
    | ExprPred (loc, expr) ->
      List [ Symbol "pred-expression"
           ; sexpr_of_expr expr ]
    | WAccess _       -> unsupported "WAccess"
    | WCallPred _     -> unsupported "WCallPred"
    | InstCallPred _  -> unsupported "InstCallPred"
    | WInstCallPred _ -> unsupported "WInstCallPred"
    | SwitchPred _    -> unsupported "SwitchPred"
    | CoefPred _      -> unsupported "CoefPred"

let sexpr_of_loop_spec (spec : loop_spec) : sexpression =
  match spec with
    | LoopInv pred     -> List [ Symbol "loop-invariant"
                               ; sexpr_of_pred pred ]
    | LoopSpec (p, q)  -> List [ Symbol "loop-spec"
                               ; sexpr_of_pred p
                               ; sexpr_of_pred q ]

let rec sexpr_of_stmt (stmt : stmt) : sexpression =
  match stmt with
    | PureStmt (loc, stmt) -> List [ Symbol "stmt-pure"
                                   ; sexpr_of_stmt stmt ]
    | Open (loc, expr, name, types, pats, args, frac) ->
      let expr =
        match expr with
          | Some expr -> [ "expression", sexpr_of_expr expr ]
          | None      -> []
      in
      let kwargs =
        [ "name", Symbol name
        ; "types", List (List.map sexpr_of_type_expr types)
        ; "patterns", List (List.map sexpr_of_pat pats)
        ; "arguments", List (List.map sexpr_of_pat args) ] @ expr
      in
      build_list [ Symbol "stmt-open" ] kwargs
    | Close (loc, expr, name, types, pats, args, frac) ->
      let expr =
        match expr with
          | Some expr -> [ "expression", sexpr_of_expr expr ]
          | None      -> []
      in
      let kwargs =
        [ "name", Symbol name
        ; "types", List (List.map sexpr_of_type_expr types)
        ; "patterns", List (List.map sexpr_of_pat pats)
        ; "arguments", List (List.map sexpr_of_pat args) ] @ expr
      in
      build_list [ Symbol "stmt-close" ] kwargs                 
    | IfStmt (loc, cond, then_stmt, else_stmt) ->
      List [ Symbol "stmt-if"
           ; sexpr_of_expr cond
           ; List ( Symbol "begin" :: List.map sexpr_of_stmt then_stmt )
           ; List ( Symbol "begin" :: List.map sexpr_of_stmt else_stmt ) ]
    | BlockStmt (loc, decls, stmts, _ , _) ->
      List [ Symbol "stmt-begin"
           ; List (List.map sexpr_of_decl decls)
           ; List (List.map sexpr_of_stmt stmts) ]
    | ExprStmt expr ->
      List [ Symbol "stmt-expression"
           ; sexpr_of_expr expr ]
    | WhileStmt (loc, cond, invariant, expr, body) ->
      build_list [ Symbol "stmt-while" ]
                 [ "condition", sexpr_of_expr cond
                 ; "invariant", sexpr_of_option sexpr_of_loop_spec invariant
                 ; "unknown", sexpr_of_option sexpr_of_expr expr
                 ; "body", sexpr_of_list sexpr_of_stmt body ]
    | DeclStmt (loc, type_expr, xs) ->
      let sexpr_of_local (str, expr, address) =
        let initialization =
          match expr with
            | Some expr -> [ "init", sexpr_of_expr expr ]
            | None      -> []
        in
        let address =
          [ "pointer", sexpr_of_bool !address ]
        in
        build_list [ Symbol "local"
                   ; Symbol str ]
                   ( initialization @ address )
      in
      build_list [ Symbol "stmt-declaration" ]
                 [ "type", sexpr_of_type_expr type_expr
                 ; "locals", sexpr_of_list sexpr_of_local xs ]
    | ReturnStmt (loc, expr) ->
      let expr =
        match expr with
          | Some expr -> [ "value", sexpr_of_expr expr ]
          | None      -> []
      in
        build_list [ Symbol "stmt-return" ]
                   expr
    | Assert (loc, pred) ->
      List [ Symbol "stmt-assert"
           ; sexpr_of_pred pred ]
    | NonpureStmt _                          -> unsupported "stmt-NonpureStmt"
    | SwitchStmt _                           -> unsupported "stmt-SwitchStmt"
    | Leak _                                 -> unsupported "stmt-Leak"
    | PerformActionStmt _                    -> unsupported "stmt-PerformActionStmt"
    | SplitFractionStmt _                    -> unsupported "stmt-SplitFractionStmt"
    | MergeFractionsStmt _                   -> unsupported "stmt-MergeFractionsStmt"
    | CreateBoxStmt _                        -> unsupported "stmt-CreateBoxStmt"
    | CreateHandleStmt _                     -> unsupported "stmt-CreateHandleStmt"
    | DisposeBoxStmt _                       -> unsupported "stmt-DisposeBoxStmt"
    | LabelStmt _                            -> unsupported "stmt-LabelStmt"
    | GotoStmt _                             -> unsupported "stmt-GotoStmt"
    | NoopStmt _                             -> unsupported "stmt-NoopStmt"
    | InvariantStmt _                        -> unsupported "stmt-InvariantStmt"
    | ProduceLemmaFunctionPointerChunkStmt _ -> unsupported "stmt-ProduceLemmaFunctionPointerChunkStmt"
    | ProduceFunctionPointerChunkStmt _      -> unsupported "stmt-ProduceFunctionPointerChunkStmt"
    | Throw _                                -> unsupported "stmt-Throw"
    | TryCatch _                             -> unsupported "stmt-TryCatch"
    | TryFinally _                           -> unsupported "stmt-TryFinally"
    | Break _                                -> unsupported "stmt-Break"

and sexpr_of_decl (decl : decl) : sexpression =
  let symbol s = Symbol s
  in
  match decl with
    | Struct (loc,
              name,
              None) ->
        List [ Symbol "declare-struct"
             ; Symbol name ]
    | Struct (loc,
              name,
              Some fields) ->
        build_list [ Symbol "define-struct"
                   ; Symbol name ]
                   [ "fields", sexpr_of_list ~head:(Some (Symbol "fields")) sexpr_of_field fields ]
    | Func (loc,
            kind,
            tparams,
            rtype,
            name,
            params,
            atom,
            impl,
            contract,
            body,
            binding,
            visibility) ->
      let sexpr_of_arg (t, id) =
        List [ Symbol id; sexpr_of_type_expr t ]
      in
      let body =
        match body with
          | None           -> [ ]
          | Some (body, _) -> [ "body", List (List.map sexpr_of_stmt body) ]
      in
      let contract =
        match contract with
          | None -> []
          | Some (pre, post) -> [ "precondition", sexpr_of_pred pre
                                ; "postcondition", sexpr_of_pred post ]
      in
      let kw = List.concat [ [ "kind", sexpr_of_func_kind kind
                             ; "type-parameters", List (List.map symbol tparams)
                             ; "return-type", sexpr_of_type_expr_option rtype
                             ; "parameters", List (List.map sexpr_of_arg params) ]
                           ; body
                           ; contract ]
      in
        build_list [ Symbol "declare-function"; Symbol name ] kw
    | PredFamilyDecl (loc,
                      name,
                      tparams,
                      index_count,
                      params,
                      precise) ->
      build_list [ Symbol "declare-predicate-family"
                 ; Symbol name ]
                 [ "type-parameters", List (List.map symbol tparams)
                 ; "parameters", List (List.map sexpr_of_type_expr params)
                 ; "index-count", sexpr_of_int index_count ]
    | PredFamilyInstanceDecl (loc,
                              name,
                              tparams,
                              _,
                              params,
                              predicate) ->
      let arg_pair (t, s) =
        List [ Symbol s
             ; sexpr_of_type_expr t ]
      in
      build_list [ Symbol "declare-predicate-family-instance"
                 ; Symbol name ]
                 [ "type-parameters", List (List.map symbol tparams)
                 ; "parameters", List (List.map arg_pair params)
                 ; "predicate", sexpr_of_pred predicate ]
    | Inductive _                 -> unsupported "Inductive"
    | Class _                     -> unsupported "Class"
    | Interface _                 -> unsupported "Interface"
    | PredCtorDecl _              -> unsupported "PredCtorDecl"
    | FuncTypeDecl _              -> unsupported "FuncTypeDecl"
    | BoxClassDecl _              -> unsupported "BoxClassDecl"
    | EnumDecl _                  -> unsupported "EnumDecl"
    | Global _                    -> unsupported "Global"
    | UnloadableModuleDecl _      -> unsupported "UnloadableModuleDecl"

let sexpr_of_import (Import (loc, name, entry)) : sexpression =
  List [ Symbol "import"
       ; Symbol name
       ; match entry with
         | None   -> Symbol "*"
         | Some s -> Symbol s ]

let sexpr_of_package (PackageDecl (loc, name, imports, declarations)) : sexpression =
  build_list [ Symbol "declare-package"
             ; Symbol name ]
             [ "imports", sexpr_of_list sexpr_of_import imports
             ; "declarations", let head = Some (Symbol "declarations")
                               in
                               sexpr_of_list ~head:head sexpr_of_decl declarations ]

let with_open_file (filename : string) (func : out_channel -> unit) : unit =
  let channel = open_out filename in
  try
    func channel;
    close_out channel
  with
      e -> begin 
        close_out channel;
        raise e
      end

let emit ?(margin = 160) (target_file : string) (packages : package list) : unit =
  let emit_to channel =
    let output_string = output_string channel
    in
    packages |> List.iter begin fun p ->
      output_string (string_of_sexpression $. sexpr_of_package p);
      output_string "\n"
    end
  in
  with_open_file target_file emit_to
