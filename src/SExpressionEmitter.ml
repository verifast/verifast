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
    | Int (Signed, CharRank)  -> aux2 "type-char"
    | Int (Unsigned, CharRank) -> aux2 "type-uchar"
    | Int (Signed, ShortRank) -> aux2 "type-short"
    | Int (Unsigned, ShortRank) -> aux2 "type-ushort"
    | Int (Signed, IntRank)   -> aux2 "type-int"
    | Int (Unsigned, IntRank) -> aux2 "type-uint"
    | Int (Signed, LongRank)  -> aux2 "type-long"
    | Int (Unsigned, LongRank)-> aux2 "type-ulong"
    | Int (Signed, LongLongRank) -> aux2 "type-llong"
    | Int (Unsigned, LongLongRank) -> aux2 "type-ullong"
    | Int (Signed, PtrRank)   -> aux2 "type-intptr"
    | Int (Unsigned, PtrRank) -> aux2 "type-uintptr"
    | Int (Signed, FixedWidthRank n) -> aux2 ("type-int" ^ string_of_int ((1 lsl n) * 8))
    | Int (Unsigned, FixedWidthRank n) -> aux2 ("type-uint" ^ string_of_int ((1 lsl n) * 8))
    | RealType                -> aux2 "type-real"
    | Float                   -> aux2 "type-float"
    | Double                  -> aux2 "type-double"
    | LongDouble              -> aux2 "type-long-double"
    | StructType s            -> List [ Symbol "type-struct"; Symbol s ]
    | UnionType s             -> List [ Symbol "type-union"; Symbol s ]
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
    | ObjType (s, targs)      -> List [ Symbol "type-obj-type";
                                        Symbol s;
                                        Symbol "type-arguments";
                                        sexpr_of_list sexpr_of_type_ targs]
    | ArrayType (t)           -> List [ Symbol "type-array-type";
                                        sexpr_of_type_ t ]
    | StaticArrayType (t, n)  -> List [ Symbol "type-static-array-type";
                                        sexpr_of_type_ t;
                                        Number (Big_int.big_int_of_int n) ]
    | BoxIdType               -> aux2 "type-box-id"
    | HandleIdType            -> aux2 "type-handle-id-type"
    | AnyType                 -> aux2 "AnyType"
    | RealTypeParam s         -> List [ Symbol "real-type-param"; Symbol s ]
    | InferredRealType s      -> List [ Symbol "inferred-real-type"; Symbol s ]
    | GhostTypeParam s        -> List [ Symbol "ghost-type-param"; Symbol s ]
    | InferredType (_, i)     -> List [ Symbol "type-inferred"; sexpr_of_inferred_type_state !i]
    | ClassOrInterfaceName (s)-> List [ Symbol "type-class-or-interface-name"; Symbol s ]
    | PackageName (s)         -> List [ Symbol "type-package-name"; Symbol s ]
    | RefType (t)             -> List [ Symbol "type-ref-type"; sexpr_of_type_ t ]
    | AbstractType (s)        -> List [ Symbol "type-abstract"; Symbol s ]
and sexpr_of_inferred_type_state = function
    Unconstrained -> List [ Symbol "inferred-type-state-unconstrained" ]
  | ContainsAnyConstraint allowContainsAnyPositive -> List [ Symbol "inferred-type-state-contains-any-constraint"; sexpr_of_bool allowContainsAnyPositive ]
  | EqConstraint t -> List [ Symbol "inferred-type-state-eq-constraint"; sexpr_of_type_ t ]

let rec sexpr_of_type_expr : type_expr -> sexpression = function
  | StructTypeExpr (_, name, _, _) ->
      List [ Symbol "type-expr-struct"; sexpr_of_option (fun s -> Symbol s) name ]
  | UnionTypeExpr (_, name, _) ->
      List [ Symbol "type-expr-union"; sexpr_of_option (fun s -> Symbol s) name ]
  | EnumTypeExpr (_, name, _) ->
      List [ Symbol "type-expr-enum"; sexpr_of_option (fun s -> Symbol s) name ]
  | PtrTypeExpr (_, te) ->
      List [ Symbol "type-expr-pointer-to"; sexpr_of_type_expr te ]
  | FuncTypeExpr (_, rte, ps) ->
      List [ Symbol "type-expr-func"; sexpr_of_type_expr rte; List (List.map (fun (te, x) -> List [ sexpr_of_type_expr te; Symbol x ]) ps) ]
  | ManifestTypeExpr (_, t) ->
      List [ Symbol "type-expr-manifest"; sexpr_of_type_ t ]
  | ArrayTypeExpr (_, te) ->
      List [ Symbol "type-expr-array-type"; sexpr_of_type_expr te ]
  | StaticArrayTypeExpr (_, te, n) ->
      List [ Symbol "type-expr-static-array"; sexpr_of_type_expr te; sexpr_of_int n ]
  | IdentTypeExpr (_, package, name) ->
      build_list
        [ Symbol "type-expr-ident" ]
        [ "package", Symbol (match package with None -> "" | Some x -> x); "name", Symbol name ]
  | ConstructedTypeExpr (_, x, targs) ->
      build_list
        [ Symbol "type-expr-constructed" ]
        [ "gen-type", Symbol x; "type-args", sexpr_of_list sexpr_of_type_expr targs ]
  | PredTypeExpr (_, targs, p) ->
      build_list
        [ Symbol "type-pred-expr" ]
        [ "types", sexpr_of_list sexpr_of_type_expr targs; "precise", sexpr_of_option sexpr_of_int p ]
  | PureFuncTypeExpr (_, exprs) ->
      build_list
        [ Symbol "type-expr-pure-func" ]
        [ "type-exprs", sexpr_of_list sexpr_of_type_expr exprs ]
  | LValueRefTypeExpr (_, te) -> 
      List [ Symbol "type-expr-lvalue-ref"; sexpr_of_type_expr te ]

let sexpr_of_type_expr_option : type_expr option -> sexpression = function
  | Some t -> sexpr_of_type_expr t
  | None   -> Symbol "nil"

let sexpr_of_attr : struct_attr -> sexpression = function
  | Packed -> Symbol "packed"

let sexpr_of_field (Field (loc, ghostness, type_expr, name, binding, visibility, final, expr)) : sexpression =
  build_list
    [ Symbol name ]
    [ "ghostness", sexpr_of_ghostness ghostness
    ; "type", sexpr_of_type_expr type_expr ]

let sexpr_of_base (CxxBaseSpec (loc, name, virt)) : sexpression =
  build_list
    [ Symbol name ]
    [ "virtual", sexpr_of_bool virt ]

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
    | ClassOrInterfaceNameScope
                         -> Symbol "class-or-interface-name"
    | PackageNameScope   -> Symbol "package-name"

let sexpr_of_operator (op : operator) : sexpression =
  match op with
    | Add         -> Symbol "+"
    | Sub         -> Symbol "-"
    | PtrDiff     -> Symbol "p-"
    | Le          -> Symbol "<="
    | Lt          -> Symbol "<"
    | Ge          -> Symbol ">="
    | Gt          -> Symbol ">"
    | Eq          -> Symbol "="
    | Neq         -> Symbol "!="
    | And         -> Symbol "&"
    | Or          -> Symbol "|"
    | Xor         -> Symbol "^^"
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
    | MinValue t  -> List [Symbol "MinValue"; sexpr_of_type_ t]
    | MaxValue t  -> List [Symbol "MaxValue"; sexpr_of_type_ t]

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

let sexpr_of_predref (p: predref) : sexpression =
  build_list
    [ Symbol "pred-ref" ]
    [
      "name", Symbol p#name;
      "domain", sexpr_of_list sexpr_of_type_ p#domain;
      "inputParamCount", sexpr_of_option sexpr_of_int p#inputParamCount
    ]


let rec sexpr_of_expr (expr : expr) : sexpression =
  let sexpr_of_tparam t = Symbol t in
  match expr with
    | True loc  -> Symbol "expr-true"
    | False loc -> Symbol "expr-false"
    | Null loc  -> Symbol "expr-null"
    | Var (loc, name) -> build_list [ Symbol "expr-var"; Symbol name ] []
    | WVar (loc, name, scope) ->
        let scope_kw = [ "scope", sexpr_of_ident_scope scope ] in
        build_list [ Symbol "expr-wvar"; Symbol name ] scope_kw
    | Select (loc, expr, str) ->
      List [ Symbol "expr-select"
           ; sexpr_of_expr expr
           ; Symbol str ]
    | IntLit (loc, n, is_decimal, usuffix, lsuffix) ->
        build_list [ Symbol "expr-int"; Number n ] []
    | WIntLit (loc, n) ->
        build_list [ Symbol "expr-wintlit"; Number n ] []
    | RealLit (_, num, suffix) ->
        build_list
          [ Symbol "expr-real-lit" ]
          [
            "num", Symbol (Num.string_of_num num);
            "suffix", sexpr_of_option (function FloatFSuffix -> Symbol "f" | FloatLSuffix -> Symbol "l") suffix
          ]
    | StringLit (_, s) ->
        List [ Symbol "expr-string-literal"; Symbol s ]
    | ClassLit (_, cn) ->
        List [ Symbol "expr-class-lit"; Symbol cn ]
    | TruncatingExpr (loc, e) ->
        build_list [ Symbol "expr-truncating"; sexpr_of_expr e ] []
    | Operation (loc, op, exprs) ->
        build_list
          [ Symbol "expr-op"; sexpr_of_operator op ]
          [ "operands", List (List.map sexpr_of_expr exprs) ]
    | WOperation (loc, op, exprs, type_) ->
        build_list
          [ Symbol "expr-wop"; sexpr_of_operator op ]
          [ "operands", List (List.map sexpr_of_expr exprs); "type", sexpr_of_type_ type_ ]
    | SliceExpr (_, ps1, ps2) ->
        build_list
          [ Symbol "expr-slice-expr" ]
          [
            "ps1", sexpr_of_option sexpr_of_pat ps1;
            "ps2", sexpr_of_option sexpr_of_pat ps2
          ]
    | Read (loc, expr, str) ->
        List [ Symbol "expr-read"; sexpr_of_expr expr; Symbol str ]
    | ArrayLengthExpr (_, e) ->
        List [ Symbol "expr-array-length"; sexpr_of_expr e ]
    | WRead (_, e, par, name, range, stat, cons, ghost) ->
        build_list
          [ Symbol "expr-w-read" ]
          [
            "e", sexpr_of_expr e;
            "par", Symbol par;
            "name", Symbol name;
            "range", sexpr_of_type_ range;
            "stat", sexpr_of_bool stat;
            "cons", sexpr_of_option (sexpr_of_option sexpr_of_constant_value) !cons;
            "ghost", sexpr_of_ghostness ghost
          ]
    | WSelect (_, e, par, name, range) ->
      build_list [ Symbol "expr-w-select" ]
                 [ "e", sexpr_of_expr e
                 ; "par", Symbol par
                 ; "name", Symbol name
                 ; "range", sexpr_of_type_ range ]
    | WReadInductiveField (loc, e, i, c, f, targs) ->
      build_list
        [ Symbol "expr-wreadinductivefield" ]
        [
          "e", sexpr_of_expr e;
          "ind", Symbol i;
          "ctor", Symbol c;
          "field", Symbol f;
          "targs", sexpr_of_list sexpr_of_type_ targs
        ]
    | ReadArray (_, lhs, rhs) ->
      build_list
        [ Symbol "expr-read-array" ]
        [
          "lhs", sexpr_of_expr lhs;
          "rhs", sexpr_of_expr rhs
        ]
    | WReadArray (_, lhs, t, rhs) ->
      build_list
        [ Symbol "expr-w-read-array" ]
        [
          "lhs", sexpr_of_expr lhs;
          "t", sexpr_of_type_ t;
          "rhs", sexpr_of_expr rhs
        ]
    | Deref (_, e) ->
        build_list [ Symbol "expr-deref" ] [ "e", sexpr_of_expr e]
    | WDeref (_, e, t) ->
        build_list
          [ Symbol "expr-w-deref" ]
          [ "e", sexpr_of_expr e; "t", sexpr_of_type_ t ]
    | CallExpr (loc, name, targs, indices, args, binding) ->
        build_list
          [ Symbol "expr-call"; Symbol name ]
          [
            "type-arguments", List (List.map sexpr_of_type_expr targs);
            "indices", List (List.map sexpr_of_pat indices);
            "arguments", List (List.map sexpr_of_pat args);
            "binding", sexpr_of_method_binding binding
          ]
    | ExprCallExpr (_, expr, args) ->
      build_list
        [ Symbol "expr-call-expr" ]
        [
          "expr", sexpr_of_expr expr;
          "args", sexpr_of_list sexpr_of_expr args
        ]
    | WFunPtrCall (_, callee, ftn, exprs) ->
      build_list
        [ Symbol "expr-w-func-ptr-call" ]
        [
          "callee", sexpr_of_expr callee;
          "function-type", Symbol ftn;
          "exprs", sexpr_of_list sexpr_of_expr exprs
        ]
    | WPureFunCall (_, name, typs, exprs) ->
      build_list
        [ Symbol "expr-w-pure-func-call" ]
        [
          "name", Symbol name;
          "typs", sexpr_of_list sexpr_of_type_ typs;
          "exprs", sexpr_of_list sexpr_of_expr exprs
        ]
    | WPureFunValueCall (_, expr, exprs) ->
      build_list
        [ Symbol "expr-w-pure-func-value-call" ]
        [
          "expr", sexpr_of_expr expr;
          "exprs", sexpr_of_list sexpr_of_expr exprs
        ]
    | WFunCall  (_, name, typs, exprs, _) ->
      build_list
        [ Symbol "expr-w-func-call" ]
        [
          "name", Symbol name;
          "typs", sexpr_of_list sexpr_of_type_ typs;
          "exprs", sexpr_of_list sexpr_of_expr exprs
        ]
    | WMethodCall (_, clss, name, typs, exprs, bind, tparamEnv) ->
        build_list
          [ Symbol "expr-w-method-call" ]
          [
            "class", Symbol clss;
            "name", Symbol name;
            "typs", sexpr_of_list sexpr_of_type_ typs;
            "exprs", sexpr_of_list sexpr_of_expr exprs;
            "stat", sexpr_of_method_binding bind;
            "tparams", sexpr_of_list sexpr_of_tparam (List.map (fun (tparam,targ) -> tparam) tparamEnv);
            "targs", sexpr_of_list sexpr_of_type_ (List.map (fun (_,targ) -> targ) tparamEnv)
          ]
    | NewArray (_, texpr, expr) ->
        build_list
          [ Symbol "expr-new-array" ]
          [ "texpr", sexpr_of_type_expr texpr; "expr", sexpr_of_expr expr ]
    | NewObject (l, cn, args, targs) ->
        build_list
          [ Symbol "expr-new-obj"; Symbol cn ]
          [
            "args", sexpr_of_list sexpr_of_expr args;
            "targs", sexpr_of_option (fun targs -> sexpr_of_list sexpr_of_type_expr targs) targs
          ]
    | CxxDelete (_, e) ->
        build_list
          [ Symbol "expr-delete" ]
          [
            "expr", sexpr_of_expr e
          ]
    | NewArrayWithInitializer (l, texpr, args) ->
        build_list
          [ Symbol "expr-array-init" ]
          [
            "type", sexpr_of_type_expr texpr;
            "init", sexpr_of_list sexpr_of_expr args
          ]
    | IfExpr (_, c, e1, e2) ->
        build_list
          [ Symbol "expr-if" ]
          [
            "cond", sexpr_of_expr c;
            "e1", sexpr_of_expr e1;
            "e2", sexpr_of_expr e2
          ]
    | SwitchExpr (_, cond, clauses, default) ->
        build_list
          [ Symbol "expr-switch" ]
          [
            "cond", sexpr_of_expr cond;
            "clauses", sexpr_of_list sexpr_of_switch_clause clauses;
            "default", sexpr_of_option (fun (_, e) -> sexpr_of_expr e) default
          ]
    | WSwitchExpr (_, cond, ind_type, typs, clauses, default, tparamEnv, result_type) ->
        build_list
          [ Symbol "expr-switch" ]
          [
            "cond", sexpr_of_expr cond;
            "ind-type", Symbol ind_type;
            "typs", sexpr_of_list sexpr_of_type_ typs;
            "clauses", sexpr_of_list sexpr_of_switch_clause clauses;
            "default", sexpr_of_option (fun (_, e) -> sexpr_of_expr e) default;
            "tparams", sexpr_of_list sexpr_of_tparam (List.map (fun (tparam,targ) -> tparam) tparamEnv);
            "targs", sexpr_of_list sexpr_of_type_ (List.map (fun (_,targ) -> targ) tparamEnv);
            "result-type", sexpr_of_type_ result_type
          ]
    | PredNameExpr (_, name) ->
        List [ Symbol "expr-pred-name"; Symbol name ]
    | CastExpr (_, texpr, expr) ->
        build_list
          [ Symbol "expr-cast" ]
          [ "typ", sexpr_of_type_expr texpr; "expr", sexpr_of_expr expr ]
    | Upcast (e, t1, t2) ->
        build_list
          [ Symbol "expr-upcast" ]
          [
            "e", sexpr_of_expr e;
            "t1", sexpr_of_type_ t1;
            "t2", sexpr_of_type_ t2
          ]
    | TypedExpr (e, t) ->
        build_list
          [ Symbol "expr-typed" ]
          [
            "e", sexpr_of_expr e;
            "t", sexpr_of_type_ t
          ]
    | WidenedParameterArgument (e) ->
        build_list
          [ Symbol "expr-widened-param-arg" ]
          [ "e", sexpr_of_expr e ]
    | SizeofExpr (loc, TypeExpr texpr) ->
        List [ Symbol "expr-sizeof"; sexpr_of_type_expr texpr ]
    | SizeofExpr (loc, e) ->
        List [ Symbol "expr-sizeof-expr"; sexpr_of_expr e ]
    | GenericExpr (loc, e, cases, def) ->
        List [ Symbol "expr-generic"; sexpr_of_expr e;
          List (cases |> List.map (fun (te, e) -> List [ sexpr_of_type_expr te; sexpr_of_expr e ]));
          sexpr_of_option sexpr_of_expr def
        ]
    | AddressOf (_, e) ->
        List [ Symbol "expr-address-of"; sexpr_of_expr e ]
    | ProverTypeConversion (t1, t2, e) ->
        build_list
          [ Symbol "expr-prover-type-conversion" ]
          [
            "t1", sexpr_of_prover_type t1;
            "t2", sexpr_of_prover_type t2;
            "e", sexpr_of_expr e
          ]
    | ArrayTypeExpr' (_, e) ->
        build_list
          [ Symbol "expr-array-type" ]
          [ "e", sexpr_of_expr e ]
    | AssignExpr (loc, lhs, rhs) ->
        List [ Symbol "expr-assign"; sexpr_of_expr lhs; sexpr_of_expr rhs ]
    | AssignOpExpr (loc, lhs, op, rhs, post) ->
        build_list
          [ Symbol "expr-assign-op" ]
          [
            "lhs", sexpr_of_expr lhs;
            "rhs", sexpr_of_expr rhs;
            "op", sexpr_of_operator op;
            "post", sexpr_of_bool post
          ]
    | WAssignOpExpr (loc, lhs, op, rhs, post) ->
        build_list
          [ Symbol "expr-wassign-op" ]
          [
            "lhs", sexpr_of_expr lhs;
            "rhs", sexpr_of_expr rhs;
            "op", Symbol op;
            "post", sexpr_of_bool post
          ]
    | InstanceOfExpr (_, expr, texpr) ->
        build_list
          [ Symbol "expr-instance-of" ]
          [ "expr", sexpr_of_expr expr; "texpr", sexpr_of_type_expr texpr ]
    | SuperMethodCall (_, name, params) ->
        build_list
          [ Symbol "expr-super-call" ]
          [ "name", Symbol name; "params", sexpr_of_list sexpr_of_expr params ]
    | WSuperMethodCall (_, _, name, params, _) ->
        build_list
          [ Symbol "expr-w-super-call" ]
          [ "name", Symbol name; "params", sexpr_of_list sexpr_of_expr params ]
    | InitializerList (_, exprs) ->
        build_list
          [ Symbol "expr-init-list" ]
          [ "exprs", sexpr_of_list sexpr_of_expr exprs ]
    | PointsTo (loc, expr, pat) ->
        build_list
          [ Symbol "expr-points-to" ]
          [
            "expr", sexpr_of_expr expr;
            "pat", sexpr_of_pat pat
          ]
    | WPointsTo (loc, expr, t, pat) ->
        build_list
          [ Symbol "expr-w-points-to" ]
          [
            "expr", sexpr_of_expr expr;
            "type", sexpr_of_type_ t;
            "pat", sexpr_of_pat pat
          ]
    | PredAsn (loc, name, typs, pats1, pats2) ->
        build_list
          [ Symbol "expr-pred-asn" ]
          [
            "name", Symbol name;
            "typs", sexpr_of_list sexpr_of_type_expr typs;
            "pats1", sexpr_of_list sexpr_of_pat pats1;
            "pats2", sexpr_of_list sexpr_of_pat pats2;
          ]
    | WPredAsn (loc, pred_ref, global, typs, pats1, pats2) ->
        build_list
          [ Symbol "expr-w-pred-asn" ]
          [
            "pred_ref", sexpr_of_predref pred_ref;
            "global", sexpr_of_bool global;
            "typs", sexpr_of_list sexpr_of_type_ typs;
            "pats1", sexpr_of_list sexpr_of_pat pats1;
            "pats2", sexpr_of_list sexpr_of_pat pats2;
          ]
    | InstPredAsn (loc, expr1, name, expr2, pats) ->
        build_list
          [ Symbol "expr-inst-pred-asn" ]
          [
            "expr1", sexpr_of_expr expr1;
            "name", Symbol name;
            "expr2", sexpr_of_expr expr2;
            "pats", sexpr_of_list sexpr_of_pat pats;
          ]
    | WInstPredAsn (loc, expr1, static_type, static_type_fin, family, instance_pred_name, expr2, pats) ->
        build_list
          [ Symbol "expr-w-inst-pred-asn" ]
          [
            "expr1", sexpr_of_option sexpr_of_expr expr1;
            "static-type", Symbol static_type;
            "static-type-finality", sexpr_of_class_finality static_type_fin;
            "family", Symbol family;
            "instance-pred-name", Symbol instance_pred_name;
            "expr2", sexpr_of_expr expr2;
            "pats", sexpr_of_list sexpr_of_pat pats;
          ]
    | ExprAsn (loc, expr) ->
        build_list [ Symbol "expr-asn" ] [ "expr", sexpr_of_expr expr ]
    | Sep (loc, asn1, asn2) ->
        build_list [ Symbol "expr-sep" ] [ "asn1", sexpr_of_expr asn1; "asn2", sexpr_of_expr asn2 ]
    | IfAsn (loc, expr, asn1, asn2) ->
        build_list
          [ Symbol "expr-if-asn" ]
          [
            "expr", sexpr_of_expr expr;
            "asn1", sexpr_of_expr asn1;
            "asn2", sexpr_of_expr asn2
          ]
    | SwitchAsn (loc, expr, clauses) ->
        build_list
          [ Symbol "expr-switch-asn" ]
          [
            "expr", sexpr_of_expr expr;
            "clauses", sexpr_of_list sexpr_of_switch_asn_clause clauses
          ]
    | WSwitchAsn (loc, expr, inductive_type, clauses) ->
        build_list
          [ Symbol "expr-w-switch-asn" ]
          [
            "expr", sexpr_of_expr expr;
            "inductive-type", Symbol inductive_type;
            "clauses", sexpr_of_list sexpr_of_wswitch_asn_clause clauses
          ]
    | EmpAsn (loc) -> List [ Symbol "expr-emp-asn" ]
    | ForallAsn (loc, typ, i, expr) ->
        build_list
          [ Symbol "expr-forall-asn" ]
          [
            "typ", sexpr_of_type_expr typ;
            "i", Symbol i;
            "expr", sexpr_of_expr expr
          ]
    | CoefAsn (loc, pat, asn) ->
        build_list
          [ Symbol "expr-coef-asn" ]
          [
            "pat", sexpr_of_pat pat;
            "asn", sexpr_of_expr asn
          ]
    | EnsuresAsn (loc, asn) ->
        build_list
          [ Symbol "expr-ensures-asn" ]
          [ "asn", sexpr_of_expr asn ]
    | MatchAsn (loc, asn, pat) ->
        build_list
          [ Symbol "expr-match-asn" ]
          [ "asn", sexpr_of_expr asn; "pat", sexpr_of_pat pat ]
    | WMatchAsn (loc, asn, pat, typ) ->
        build_list
          [ Symbol "expr-w-match-asn" ]
          [
            "asn", sexpr_of_expr asn;
            "pat", sexpr_of_pat pat;
            "typ", sexpr_of_type_ typ
          ]
    | CxxLValueToRValue (l, e) ->
        List [ Symbol "lvalue-to-rvalue"; sexpr_of_expr e ]
    | CxxDerivedToBase (l, e, te) -> 
        build_list
          [ Symbol "expr-cxx-derived-to-base" ]
          [
            "expr", sexpr_of_expr e;
            "to-base-type", sexpr_of_type_expr te
          ]


and sexpr_of_pat (pat : pat) : sexpression =
  match pat with
    | LitPat expr -> List [ Symbol "pat-lit"; sexpr_of_expr expr ]
    | VarPat (l, str) -> List [ Symbol "pat-var"; Symbol str ]
    | DummyPat -> List [ Symbol "pat-dummy" ]
    | CtorPat (l, str, pats) ->
        build_list
          [ Symbol "pat-ctor"; Symbol str ]
          [ "pats", sexpr_of_list sexpr_of_pat pats ]
    | WCtorPat (l, i, targs, name, ts0, ts, pats, e_opt) ->
        build_list
          [ Symbol "pat-w-ctor"; Symbol name ]
          [
            "i", Symbol i;
            "targs", sexpr_of_list sexpr_of_type_ targs;
            "ts0", sexpr_of_list sexpr_of_type_ ts0;
            "ts", sexpr_of_list sexpr_of_type_ ts;
            "pats", sexpr_of_list sexpr_of_pat pats;
            "e_opt", sexpr_of_option sexpr_of_expr e_opt
          ]

and sexpr_of_switch_clause (c : switch_expr_clause) : sexpression =
  match c with
    | SwitchExprClause (_, name, args, e) ->
        build_list
          [ Symbol "switch-clause"; Symbol name ]
          [ "args", sexpr_of_list (fun x -> Symbol x) args; "body", sexpr_of_expr e ]

and sexpr_of_switch_asn_clause (c: switch_asn_clause) : sexpression =
  match c with
    | SwitchAsnClause (loc, name, l, expr) ->
        build_list
          [ Symbol "switch-asn-clause" ]
          [
            "name", Symbol name;
            "l", sexpr_of_list (fun x -> Symbol x) l;
            "expr", sexpr_of_expr expr
          ]

and sexpr_of_wswitch_asn_clause (c: wswitch_asn_clause) : sexpression =
  match c with
    | WSwitchAsnClause (loc, name, l, ptypes, expr) ->
        build_list
          [ Symbol "w-switch-asn-clause" ]
          [
            "name", Symbol name;
            "l", sexpr_of_list (fun x -> Symbol x) l;
            "ptypes", sexpr_of_list (sexpr_of_option sexpr_of_prover_type) ptypes;
            "expr", sexpr_of_expr expr
          ]

and sexpr_of_class_finality (f: class_finality) : sexpression =
  match f with
      | FinalClass -> Symbol "final-class"
      | ExtensibleClass -> Symbol "extensible-class"

and sexpr_of_prover_type (t : prover_type) : sexpression =
  match t with
  | ProverInt        -> Symbol "prover-type-int"
  | ProverBool       -> Symbol "prover-type-bool"
  | ProverReal       -> Symbol "prover-type-real"
  | ProverInductive  -> Symbol "prover-type-inductive"

let rec sexpr_of_pred (asn : asn) : sexpression =
  match asn with
    | True _ -> List [ Symbol "true" ]
    | False _ -> List [ Symbol "false" ]
    | Null _ -> List [ Symbol "null" ]
    | IfAsn (loc, expr, thenp, elsep) ->
      List [ Symbol "pred-if"
           ; sexpr_of_expr expr
           ; sexpr_of_pred thenp
           ; sexpr_of_pred elsep ]
    | PredAsn (loc, p, types, indices, patterns) ->
      build_list [ Symbol "pred-call-predicate"
                 ; Symbol p ]
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
    | CoefAsn (_, pat, asn) ->
      List [ Symbol "pred-coef-asn";
             sexpr_of_pat pat;
             sexpr_of_pred asn ]
    | _ -> List [ Symbol "pred"; sexpr_of_expr asn ]

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
    | WhileStmt (loc, cond, invariant, expr, body, final_ss) ->
      build_list [ Symbol "stmt-while" ]
                 [ "condition", sexpr_of_expr cond
                 ; "invariant", sexpr_of_option sexpr_of_loop_spec invariant
                 ; "unknown", sexpr_of_option sexpr_of_expr expr
                 ; "body", sexpr_of_list sexpr_of_stmt body
                 ; "final-ss", sexpr_of_list sexpr_of_stmt final_ss ]
    | DeclStmt (loc, xs) ->
      let sexpr_of_local (lx, tx, str, expr, _) =
        let initialization =
          match expr with
            | Some expr -> [ "init", sexpr_of_expr expr ]
            | None      -> []
        in
        build_list [ Symbol "local"
                   ; Symbol str ]
                   initialization
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
    | LabelStmt (loc, lbl) ->
      List [ Symbol "stmt-label"; Symbol lbl ]
    | GotoStmt (loc, lbl) ->
      List [ Symbol "stmt-goto"; Symbol lbl ]
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
              None,
              attrs) ->
        build_list [ Symbol "declare-struct"
                   ; Symbol name ]
                   [ "attrs", sexpr_of_list ~head:(Some (Symbol "attrs")) sexpr_of_attr attrs ]
    | Struct (loc,
              name,
              Some (bases, fields, inst_preds, polymorphic),
              attrs) ->
        build_list [ Symbol "define-struct"
                   ; Symbol name ]
                   [ "bases", sexpr_of_list ~head:(Some (Symbol "bases")) sexpr_of_base bases
                   ; "fields", sexpr_of_list ~head:(Some (Symbol "fields")) sexpr_of_field fields
                   ; "attrs", sexpr_of_list ~head:(Some (Symbol "attrs")) sexpr_of_attr attrs
                   ; "instance_preds", sexpr_of_list sexpr_of_instance_pred inst_preds
                   ; "polymorphic", sexpr_of_bool polymorphic ]
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
            is_virtual,
            overrides) ->
      let sexpr_of_arg (t, id) =
        List [ Symbol id; sexpr_of_type_expr t ]
      in
      let overrides =
        match overrides with
        | [ ] -> [ ]
        | _ -> [ "overrides", sexpr_of_list (fun s -> Symbol s) overrides ]
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
                             ; "type-parameters", List (List.map symbol tparams )
                             ; "return-type", sexpr_of_type_expr_option rtype
                             ; "parameters", List (List.map sexpr_of_arg params)
                             ; "is_virtual", sexpr_of_bool is_virtual ]
                           ; overrides
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
    | Interface (_, id, inters, fields, meths, tparams, preds) ->
      build_list [ Symbol "declare-interface"
                 ; Symbol id ]
                 [ "super-interfaces", sexpr_of_list sexpr_of_super inters
                 ; "fields", sexpr_of_list sexpr_of_field fields
                 ; "methods", sexpr_of_list sexpr_of_meths meths
                 ; "instance-preds", sexpr_of_list sexpr_of_instance_pred preds ]
    | Class (_, abs, final, id, meths, fields, cons, super, tparams, inters, preds) ->
      build_list [ Symbol "declare-class"
                 ; Symbol id ]
                 [ "super-class", sexpr_of_super super
                 ; "super-interfaces", sexpr_of_list sexpr_of_super inters
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
    | Global  (_, ty, name, init_opt) ->
      build_list [ Symbol "declare-global-var" ; Symbol name ]
                 (("type", sexpr_of_type_expr ty) :: (match init_opt with None -> [] | Some e -> ["init", sexpr_of_expr e]))
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

and sexpr_of_super (name, targs) : sexpression =
  List [ Symbol name; sexpr_of_list sexpr_of_type_expr targs ]

and sexpr_of_meths (meth : meth) : sexpression =
  match meth with
  | Meth (loc, ghost, rtype, name, params, contract, body, bind, vis, abs, tparams) ->
    let sexpr_of_tparam t =
      Symbol t
    in
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
                            ; "parameters", List (List.map sexpr_of_arg params)
                            ; "type-parameters", List (List.map sexpr_of_tparam tparams) ]
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
