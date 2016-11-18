open Util
open Ast
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
  let aux1 s = Symbol s in
  let aux2 s = List [ Symbol s ] in
  match t with
    | Bool                    -> aux2 "type-bool"
    | Void                    -> aux2 "type-void"
    | Int (Signed, 4)         -> aux2 "type-int"
    | Int (Signed, 2)         -> aux2 "type-short"
    | Int (Unsigned, 4)       -> aux2 "type-uint-ptr"
    | RealType                -> aux2 "type-real"
    | Int (Signed, 1)         -> aux2 "type-char"
    | StructType s            -> List [ Symbol "type-struct"; Symbol s ]
    | PtrType t               -> List [ Symbol "type-pointer-to"; sexpr_of_type_ t ]
    | FuncType s              -> List [ Symbol "type-function"; Symbol s ]
    | InductiveType (s, ts)   -> List ( Symbol "type-inductive" ::
                                        Symbol s ::
                                        List.map sexpr_of_type_ ts )
    | PredType (is, args, p, inductiveness)
                              -> List ( [Symbol "type-pred-type"] @ 
                                        (List.map aux1 is) @
                                        (List.map sexpr_of_type_ args) @
                                        [ sexpr_of_option sexpr_of_int p
                                          ; Symbol "coinductive"
                                          ; sexpr_of_bool (inductiveness = Inductiveness_CoInductive) ] )
    | PureFuncType (t1, t2)   -> List [ Symbol "type-pred-func-type";
                                        sexpr_of_type_ t1; 
                                        sexpr_of_type_ t2]
    | ObjType (s)             -> List [ Symbol "type-obj-type";
                                        Symbol s ]
    | ArrayType (t)           -> List [ Symbol "type-array-type";
                                        sexpr_of_type_ t ]
    | BoxIdType               -> aux2 "type-box-id"
    | HandleIdType            -> aux2 "type-handle-id-type"
    | AnyType                 -> aux2 "AnyType"
    | TypeParam (s)           -> List [ Symbol "type-param";
                                        Symbol s ]
    | InferredType (_, i)     -> List [ Symbol "type-inferred";
                                        sexpr_of_option sexpr_of_type_ !i]
    | ClassOrInterfaceName (s)-> List [ Symbol "type-class-or-interface-name";
                                        Symbol s ]
    | PackageName (s)         -> List [ Symbol "type-package-name";
                                        Symbol s ]
    | RefType (t)             -> List [ Symbol "type-ref-type";
                                        sexpr_of_type_ t ]

let rec sexpr_of_type_expr : type_expr -> sexpression = function
  | StructTypeExpr (_, name)  -> 
    List [ Symbol "type-expr-struct"
         ; Symbol name ]
  | PtrTypeExpr (_, te) -> 
    List [ Symbol "type-expr-pointer-to"
         ; sexpr_of_type_expr te ]
  | ManifestTypeExpr (_, t) -> 
    List [ Symbol "type-expr-manifest"
         ; sexpr_of_type_ t ]
  | ArrayTypeExpr (_, te) ->
    List [ Symbol "type-expr-array-type"
         ; sexpr_of_type_expr te ]
  | IdentTypeExpr (_, package, name) -> 
    build_list [ Symbol "type-expr-ident" ]
               [ "package", Symbol (match package with None -> "" | Some x -> x)
               ; "name", Symbol name ]
  | ConstructedTypeExpr (_, x, targs) -> 
    build_list [ Symbol "type-expr-constructed" ]
               [ "gen-type", Symbol x
               ; "type-args", sexpr_of_list sexpr_of_type_expr targs ]
  | PredTypeExpr (_, targs, p) -> 
    build_list [ Symbol "type-pred-expr" ]
               [ "types", sexpr_of_list sexpr_of_type_expr targs
               ; "precise", sexpr_of_option sexpr_of_int p ]
  | PureFuncTypeExpr (_, exprs) -> 
    build_list [ Symbol "type-expr-pure-func" ]
               [ "type-exprs", sexpr_of_list sexpr_of_type_expr exprs ]

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

let sexpr_of_constant_value (c : constant_value) : sexpression =
    match c with
    | IntConst i    -> Symbol ("Int constant " ^ (Big_int.string_of_big_int i))
    | BoolConst b   -> Symbol ("Bool constant " ^ (string_of_bool b))
    | StringConst s -> Symbol ("String constant " ^ s)
    | NullConst     -> Symbol "Null constant"

let sexpr_of_method_binding (binding : method_binding) : sexpression =
  match binding with
    | Static   -> Symbol "class-method"
    | Instance -> Symbol "instance-method"

let rec sexpr_of_expr (expr : expr) : sexpression =
  match expr with
    | Operation (loc, op, exprs) -> 
      build_list [ Symbol "expr-op"
                 ; sexpr_of_operator op ]
                 [ "operands", List (List.map sexpr_of_expr exprs) ]
    | WOperation (loc, op, exprs, type_) -> 
      build_list [ Symbol "expr-wop"
                 ; sexpr_of_operator op ]
                 [ "operands", List (List.map sexpr_of_expr exprs)
                 ; "type", sexpr_of_type_ type_ ]
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
    | Var (loc, name) ->
      build_list [ Symbol "expr-var"
                 ; Symbol name ]
                 []
    | WVar (loc, name, scope) ->
      let scope_kw = [ "scope", sexpr_of_ident_scope scope ] in
      build_list [ Symbol "expr-wvar"
                 ; Symbol name ]
                 scope_kw
    | Read (loc, expr, str) ->
      List [ Symbol "expr-read"
           ; sexpr_of_expr expr
           ; Symbol str ]
    | IntLit (loc, n, is_decimal, usuffix, lsuffix) ->
      build_list [ Symbol "expr-int"
                  ; Number n ]
                 [] 
    | WIntLit (loc, n) ->
      build_list [ Symbol "expr-wintlit"
                  ; Number n ]
                 []
    | AssignExpr (loc, lhs, rhs) ->
      List [ Symbol "expr-assign"
           ; sexpr_of_expr lhs
           ; sexpr_of_expr rhs ]
    | SizeofExpr (loc, texpr) ->
      List [ Symbol "expr-sizeof"
           ; sexpr_of_type_expr texpr ]
    | AssignOpExpr (loc, lhs, op, rhs, post) ->
      build_list [ Symbol "expr-assign-op" ]
                 [ "lhs", sexpr_of_expr lhs
                 ; "rhs", sexpr_of_expr rhs
                 ; "op", sexpr_of_operator op
                 ; "post", sexpr_of_bool post ]
    | StringLit (_, s)          -> List [ Symbol "expr-string-literal"; Symbol s ]
    | ClassLit (_, cn)          -> List [ Symbol "expr-class-lit"; Symbol cn ]
    | ArrayLengthExpr (_, e)    -> List [ Symbol "expr-array-length"; sexpr_of_expr e ]
    | WRead (_, e, par, name, range, stat, cons, ghost) -> 
      build_list [ Symbol "expr-w-read" ]
                 [ "e", sexpr_of_expr e
                 ; "par", Symbol par
                 ; "name", Symbol name
                 ; "range", sexpr_of_type_ range
                 ; "stat", sexpr_of_bool stat
                 ; "cons", sexpr_of_option (sexpr_of_option sexpr_of_constant_value) !cons
                 ; "ghost", sexpr_of_ghostness ghost ]
    | WReadInductiveField (loc, e, i, c, f, targs) ->
      build_list [ Symbol "expr-wreadinductivefield" ]
                 [ "e", sexpr_of_expr e
                 ; "ind", Symbol i
                 ; "ctor", Symbol c
                 ; "field", Symbol f
                 ; "targs", sexpr_of_list sexpr_of_type_ targs ]
    | ReadArray (_, rhs, lhs) ->
      build_list [ Symbol "expr-read-array" ]
                 [ "lhs", sexpr_of_expr lhs
                 ; "rhs", sexpr_of_expr rhs]
    | WReadArray (_, rhs, t, lhs) ->
      build_list [ Symbol "expr-w-read-array" ]
                 [ "lhs", sexpr_of_expr lhs
                 ; "t", sexpr_of_type_ t
                 ; "rhs", sexpr_of_expr rhs]
    | Deref (_, e, t) ->
      build_list [ Symbol "expr-deref" ]
                 [ "e", sexpr_of_expr e
                 ; "t", sexpr_of_option sexpr_of_type_ !t]
    | ExprCallExpr (_, expr, args) ->
      build_list [ Symbol "expr-call-expr" ]
                 [ "expr", sexpr_of_expr expr
                 ; "args", sexpr_of_list sexpr_of_expr args ]
    | WFunPtrCall (_, name, exprs) ->
      build_list [ Symbol "expr-w-func-ptr-call" ]
                 [ "name", Symbol name
                 ; "exprs", sexpr_of_list sexpr_of_expr exprs ]
    | WPureFunCall (_, name, typs, exprs) ->
      build_list [ Symbol "expr-w-pure-func-call" ]
                 [ "name", Symbol name
                 ; "typs", sexpr_of_list sexpr_of_type_ typs
                 ; "exprs", sexpr_of_list sexpr_of_expr exprs ]
    | WPureFunValueCall (_, expr, exprs) ->
      build_list [ Symbol "expr-w-pure-func-value-call" ]
                 [ "expr", sexpr_of_expr expr
                 ; "exprs", sexpr_of_list sexpr_of_expr exprs ]
    | WFunCall  (_, name, typs, exprs) ->
      build_list [ Symbol "expr-w-func-call" ]
                 [ "name", Symbol name
                 ; "typs", sexpr_of_list sexpr_of_type_ typs
                 ; "exprs", sexpr_of_list sexpr_of_expr exprs ]
    | WMethodCall (_, clss, name, typs, exprs, bind) ->
      build_list [ Symbol "expr-w-method-call" ]
                 [ "class", Symbol clss
                 ; "name", Symbol name
                 ; "typs", sexpr_of_list sexpr_of_type_ typs
                 ; "exprs", sexpr_of_list sexpr_of_expr exprs 
                 ; "stat", sexpr_of_method_binding bind ]
    | NewArray (_, texpr, expr) ->
      build_list [ Symbol "expr-new-array" ]
                 [ "texpr", sexpr_of_type_expr texpr
                 ; "expr", sexpr_of_expr expr]
    | NewObject (l, cn, args) ->
      build_list [ Symbol "expr-new-obj"; Symbol cn ]
                 [ "args", sexpr_of_list sexpr_of_expr args ]
    | NewArrayWithInitializer (l, texpr, args) -> 
      build_list [ Symbol "expr-array-init" ]
                 [ "type", sexpr_of_type_expr texpr
                 ; "init", sexpr_of_list sexpr_of_expr args ]
    | IfExpr (_, c, e1, e2) -> 
      build_list [ Symbol "expr-if" ]
                 [ "cond", sexpr_of_expr c
                 ; "e1", sexpr_of_expr e1
                 ; "e2", sexpr_of_expr e2 ]
    | SwitchExpr (_, cond, clauses, default, _) ->
      build_list [ Symbol "expr-switch" ]
                 [ "cond", sexpr_of_expr cond
                 ; "clauses", sexpr_of_list sexpr_of_switch_clause clauses
                 ; "default", sexpr_of_option (fun (_, e) -> sexpr_of_expr e) default ]
    | PredNameExpr (_, name) ->
       List [ Symbol "expr-pred-name"
            ; Symbol name ]
    | CastExpr (_, trunc, texpr, expr) ->
      build_list [ Symbol "expr-cast" ]
                 [ "typ", sexpr_of_type_expr texpr 
                 ; "expr", sexpr_of_expr expr ]
    | AddressOf (_, e) ->
      List [ Symbol "expr-address-of"
           ; sexpr_of_expr e ]
    | InitializerList (_, exprs) -> 
      build_list [ Symbol "expr-init-list" ]
                 [ "exprs", sexpr_of_list sexpr_of_expr exprs ]
    | SliceExpr (_, ps1, ps2) ->
      build_list [ Symbol "expr-slice-expr" ]
                 [ "ps1", sexpr_of_option sexpr_of_pat ps1 
                 ; "ps2", sexpr_of_option sexpr_of_pat ps2 ]
    | ProverTypeConversion (t1, t2, e) ->
      build_list [ Symbol "expr-prover-type-conversion" ]
                 [ "t1", sexpr_of_prover_type t1
                 ; "t2", sexpr_of_prover_type t2
                 ; "e", sexpr_of_expr e]
    | ArrayTypeExpr' (_, e) ->
      build_list [ Symbol "expr-array-type" ]
                 [ "e", sexpr_of_expr e]
    | InstanceOfExpr (_, expr, texpr) -> 
      build_list [ Symbol "expr-instance-of" ]
                 [ "expr", sexpr_of_expr expr
                 ; "texpr", sexpr_of_type_expr texpr ]
    | RealLit (_, num) ->
      build_list [ Symbol "expr-real-lit" ]
                 [ "num", Symbol (Num.string_of_num num) ]
    | Upcast (e, t1, t2) ->
      build_list [ Symbol "expr-upcast" ]
                 [ "e", sexpr_of_expr e 
                 ; "t1", sexpr_of_type_ t1 
                 ; "t2", sexpr_of_type_ t2 ]
    | WidenedParameterArgument (e) ->
      build_list [ Symbol "expr-widened-param-arg" ]
                 [ "e", sexpr_of_expr e ]
    | SuperMethodCall (_, name, params) ->
      build_list [ Symbol "expr-super-call" ]
                 [ "name", Symbol name 
                 ; "params", sexpr_of_list sexpr_of_expr params ]
    | WSuperMethodCall (_, _, name, params, _) ->
      build_list [ Symbol "expr-w-super-call" ]
                 [ "name", Symbol name 
                 ; "params", sexpr_of_list sexpr_of_expr params ]

and sexpr_of_pat (pat : pat) : sexpression =
  match pat with
    | LitPat expr            -> List [ Symbol "pat-literal"; sexpr_of_expr expr ]
    | VarPat (l, str)        -> List [ Symbol "pat-variable"; Symbol str ]
    | DummyPat               -> List [ Symbol "pat-dummy" ]
    | CtorPat (l, str, pats) -> build_list [ Symbol "pat-constructor"; Symbol str ]
                                           [ "pats", sexpr_of_list sexpr_of_pat pats ]

and sexpr_of_switch_clause (c : switch_expr_clause) : sexpression =
  match c with
  | SwitchExprClause (_, name, args, e) ->
    build_list [ Symbol "switch-clause"
               ; Symbol name ]
               [ "args", sexpr_of_list (fun x -> Symbol x) args
               ; "body", sexpr_of_expr e ]

and sexpr_of_prover_type (t : prover_type) : sexpression =
  match t with
  | ProverInt        -> Symbol "prover-type-int"
  | ProverBool       -> Symbol "prover-type-bool"
  | ProverReal       -> Symbol "prover-type-real"
  | ProverInductive  -> Symbol "prover-type-inductive"
               
let rec sexpr_of_pred (asn : asn) : sexpression =
  match asn with
    | IfAsn (loc, expr, thenp, elsep) ->
      List [ Symbol "pred-if"
           ; sexpr_of_expr expr
           ; sexpr_of_pred thenp
           ; sexpr_of_pred elsep ]
    | PredAsn (loc, predref, types, indices, patterns) ->
      build_list [ Symbol "pred-call-predicate"
                 ; Symbol predref#name ]
                 [ "types", List (List.map sexpr_of_type_expr types)
                 ; "indices", List (List.map sexpr_of_pat indices)
                 ; "arguments", List (List.map sexpr_of_pat patterns) ]
    | PointsTo (loc, expr, pat) ->
      List [ Symbol "pred-access"
           ; sexpr_of_expr expr
           ; sexpr_of_pat pat ]
    | EmpAsn loc ->
      List [ Symbol "pred-empty" ]
    | Sep (loc, l, r) ->
      List [ Symbol "pred-&*&"
           ; sexpr_of_pred l
           ; sexpr_of_pred r ]
    | ExprAsn (loc, expr) ->
      List [ Symbol "pred-expression"
           ; sexpr_of_expr expr ]
    | WPointsTo (_, expr, typ, pat) ->
      build_list [ Symbol "pred-w-points-to" ]
                 [ "expr", sexpr_of_expr expr
                 ; "typ", sexpr_of_type_ typ
                 ; "pat", sexpr_of_pat pat ]
    | WPredAsn (_, pred, glob, typs, pats1, pats2) ->
      build_list [ Symbol "pred-w-pred-asn" 
                 ; Symbol pred#name ]
                 [ "glob", sexpr_of_bool glob
                 ; "typs", sexpr_of_list sexpr_of_type_ typs
                 ; "pat1", sexpr_of_list sexpr_of_pat pats1 
                 ; "pat2", sexpr_of_list sexpr_of_pat pats2 ]
    | InstPredAsn (_, expr1, name, expr2, pats)  ->
      build_list [ Symbol "pred-inst-pred"; Symbol name ]
                 [ "expr", sexpr_of_expr expr1
                 ; "init", sexpr_of_expr expr2
                 ; "pats", sexpr_of_list sexpr_of_pat pats]
    | WInstPredAsn (_, expr, name, _, _, _, _, _) -> 
      build_list [ Symbol "pred-w-pred-asn"
                 ; Symbol name ]
                 [ "expr", sexpr_of_option sexpr_of_expr expr ]
    | SwitchAsn (_, expr, _) ->
      build_list [ Symbol "pred-switch-asn" ]
                 [ "expr", sexpr_of_expr expr]
    | CoefAsn (_, pat, _) ->
      build_list [ Symbol "pred-coef-asn" ]
                 [ "expr", sexpr_of_pat pat]

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
    | DeclStmt (loc, xs) ->
      let sexpr_of_local (lx, tx, str, expr, address) =
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
                 [ "locals", sexpr_of_list sexpr_of_local xs ]
    | ReturnStmt (loc, expr) ->
      let expr =
        match expr with
          | Some expr -> [ "value", sexpr_of_expr expr ]
          | None      -> []
      in
        build_list [ Symbol "stmt-return" ]
                   expr
    | Assert (loc, asn) ->
      List [ Symbol "stmt-assert"
           ; sexpr_of_pred asn ]
    | NonpureStmt (loc, allow, stmt) -> 
      List [ Symbol "stmt-nonpure-stmt"
           ; sexpr_of_bool allow 
           ; sexpr_of_stmt stmt ]
    | SwitchStmt (loc, switch, cases) ->
      build_list [ Symbol "stmt-switch" ]
                 [ "switch", sexpr_of_expr switch
                 ; "cases", sexpr_of_list sexpr_of_stmt_clause cases ]
    | Throw (loc, expr) ->
      List [ Symbol "stmt-throw"
           ; sexpr_of_expr expr ]
    | Leak (loc, asn) ->
      List [ Symbol "stmt-leak"
           ; sexpr_of_pred asn ]
    | PerformActionStmt _                      -> unsupported "stmt-PerformActionStmt"
    | SplitFractionStmt _                      -> unsupported "stmt-SplitFractionStmt"
    | MergeFractionsStmt _                     -> unsupported "stmt-MergeFractionsStmt"
    | CreateBoxStmt _                          -> unsupported "stmt-CreateBoxStmt"
    | CreateHandleStmt _                       -> unsupported "stmt-CreateHandleStmt"
    | DisposeBoxStmt _                         -> unsupported "stmt-DisposeBoxStmt"
    | LabelStmt _                              -> unsupported "stmt-LabelStmt"
    | GotoStmt _                               -> unsupported "stmt-GotoStmt"
    | NoopStmt _                               -> unsupported "stmt-NoopStmt"
    | InvariantStmt _                          -> unsupported "stmt-InvariantStmt"
    | ProduceLemmaFunctionPointerChunkStmt _   -> unsupported "stmt-ProduceLemmaFunctionPointerChunkStmt"
    | DuplicateLemmaFunctionPointerChunkStmt _ -> unsupported "stmt-DuplicateLemmaFunctionPointerChunkStmt"
    | ProduceFunctionPointerChunkStmt _        -> unsupported "stmt-ProduceFunctionPointerChunkStmt"
    | TryCatch (loc, stmts, catchs) ->
      build_list [ Symbol "stmt-try-catch" ]
                 [ "stmts", sexpr_of_list sexpr_of_stmt stmts ]
    | TryFinally (loc1, stmts1, loc2, stmts2) ->
      build_list [ Symbol "stmt-try-finally" ]
                 [ "stmts1", sexpr_of_list sexpr_of_stmt stmts1 
                 ; "stmts2", sexpr_of_list sexpr_of_stmt stmts2 ]
    | Break (loc) ->
      List [ Symbol "stmt-break" ]
    | SuperConstructorCall (loc, args) ->
      build_list [ Symbol "stmt-supercall" ]
                 [ "arguments", List (List.map sexpr_of_expr args) ]

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
            terminates,
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
                      precise,
                      inductiveness) ->
      build_list [ Symbol "declare-predicate-family"
                 ; Symbol name ]
                 [ "type-parameters", List (List.map symbol tparams)
                 ; "parameters", List (List.map sexpr_of_type_expr params)
                 ; "index-count", sexpr_of_int index_count
                 ; "coinductive", sexpr_of_bool (inductiveness = Inductiveness_CoInductive)]
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
    | ImportModuleDecl (loc, name) ->
      List [ Symbol "declare-import-module"
            ; Symbol name ]
    | Inductive (_, name, tparams, cons) ->
      build_list [ Symbol "declare-inductive"
                 ; Symbol name]
                 [ "tparams", List (List.map symbol tparams)
                 ; "constructors", sexpr_of_list sexpr_of_inductive_constructor cons ]
    | Interface (_, id, inters, fields, meths, preds) ->
      build_list [ Symbol "declare-interface"
                 ; Symbol id ]
                 [ "super-interfaces", List (List.map symbol inters)
                 ; "fields", sexpr_of_list sexpr_of_field fields
                 ; "methods", sexpr_of_list sexpr_of_meths meths 
                 ; "instance-preds", sexpr_of_list sexpr_of_instance_pred preds ]
    | Class (_, abs, final, id, meths, fields, cons, super, inters, preds) ->
      build_list [ Symbol "declare-class"
                 ; Symbol id ]
                 [ "super-class", symbol super
                 ; "super-interfaces", List (List.map symbol inters)
                 ; "methods", sexpr_of_list sexpr_of_meths meths 
                 ; "fields", sexpr_of_list sexpr_of_field fields
                 ; "construcors", sexpr_of_list (sexpr_of_constructor id) cons 
                 ; "instance-preds", sexpr_of_list sexpr_of_instance_pred preds ]
    | PredCtorDecl (_, name, tparams, args, precise, asn) ->
      build_list [ Symbol "declare-predicate-constructor"
                 ; Symbol name ]
                 [ "tparams", List (List.map sexpr_of_argument tparams)
                 ; "args", List (List.map sexpr_of_argument args)
                 ; "precise", sexpr_of_option sexpr_of_int precise
                 ; "ans", sexpr_of_pred asn ]
    | FuncTypeDecl _              -> unsupported "FuncTypeDecl"
    | BoxClassDecl _              -> unsupported "BoxClassDecl"
    | EnumDecl _                  -> unsupported "EnumDecl"
    | Global _                    -> unsupported "Global"
    | UnloadableModuleDecl _      -> unsupported "UnloadableModuleDecl"

and sexpr_of_argument (type_, name) =
  Symbol (name ^ " with type " ^ (string_of_sexpression(sexpr_of_type_expr type_)))
  
and sexpr_of_inductive_constructor (c : ctor) : sexpression =
  let aux (name, type_) =
    Symbol (name ^ " with type " ^ (string_of_sexpression(sexpr_of_type_expr type_)))
  in
  match c with
  | Ctor (_, name, args) ->
    build_list [ Symbol "inductive-constructor"
               ; Symbol name ]
               [ "arguments", List (List.map aux args)]

and sexpr_of_meths (meth : meth) : sexpression =
  match meth with
  | Meth (loc, ghost, rtype, name, params, contract, body, bind, vis, abs) ->
    let sexpr_of_arg (t, id) =
      List [ Symbol id; sexpr_of_type_expr t ]
    in
    let body =
      match body with
        | None           -> [ ]
        | Some ((body, _), _) -> [ "body", List (List.map sexpr_of_stmt body) ]
    in
    let contract =
      match contract with
        | None -> []
        | Some (pre, post,_,_) -> [ "precondition", sexpr_of_pred pre
                                ; "postcondition", sexpr_of_pred post ] 
    in        
    let kw = List.concat [ [ "ghos", sexpr_of_ghostness ghost
                            ; "return-type", sexpr_of_type_expr_option rtype
                            ; "parameters", List (List.map sexpr_of_arg params) ]
                          ; body
                          ; contract ]
    in
      build_list [ Symbol "declare-method"; Symbol name ] kw

and sexpr_of_constructor (name : string) (cons : cons) : sexpression =
  match cons with
  | Cons (loc, params, contract, body, vis) ->
    let sexpr_of_arg (t, id) =
      List [ Symbol id; sexpr_of_type_expr t ]
    in
    let body =
      match body with
        | None           -> [ ]
        | Some ((body, _), _) -> [ "body", List (List.map sexpr_of_stmt body) ]
    in
    let contract =
      match contract with
        | None -> []
        | Some (pre, post, _, _) -> [ "precondition", sexpr_of_pred pre
                                    ; "postcondition", sexpr_of_pred post ] 
    in        
    let kw = List.concat [ [ "parameters", List (List.map sexpr_of_arg params) ]
                          ; body
                          ; contract ]
    in
      build_list [ Symbol "declare-cons"; Symbol name ] kw

and sexpr_of_loop_spec (spec : loop_spec) : sexpression =
  match spec with
    | LoopInv asn     -> List [ Symbol "loop-invariant"
                               ; sexpr_of_pred asn ]
    | LoopSpec (p, q)  -> List [ Symbol "loop-spec"
                               ; sexpr_of_pred p
                               ; sexpr_of_pred q ]

and sexpr_of_instance_pred (pred : instance_pred_decl) : sexpression =
  match pred with
    | InstancePredDecl (_, name, params, body) ->
      let sexpr_of_arg (t, id) =
        List [ Symbol id; sexpr_of_type_expr t ]
      in
      let body =
        match body with
          | None     -> [ ]
          | Some asn -> ["body", sexpr_of_pred asn ]
      in  
      let kw = List.concat [ ["parameters", List (List.map sexpr_of_arg params)]
                           ; body ]
      in
      build_list [ Symbol "declare-instance-predicate"
                 ; Symbol name ]
                 kw
    
and sexpr_of_stmt_clause (clause : switch_stmt_clause) : sexpression =
  match clause with
  | SwitchStmtClause (loc, expr, stmts) ->
    build_list [ Symbol "clause-case" ]
               [ "match", sexpr_of_expr expr
               ; "statements", sexpr_of_list sexpr_of_stmt stmts ]
  | SwitchStmtDefaultClause (loc, stmts) ->
    build_list [ Symbol "clause-default" ]
               [ "statements", sexpr_of_list sexpr_of_stmt stmts ]

let sexpr_of_import (Import (loc, ghost, name, entry)) : sexpression =
  List [ Symbol "import"
       ; sexpr_of_ghostness ghost
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
