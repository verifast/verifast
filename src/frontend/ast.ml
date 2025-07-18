open Big_int
open Num
open Util

(* Region: Locations *)

(** Base path, relative path, line (1-based), column (1-based) *)
type srcpos = (string * int * int) (* ?srcpos *)

(** A range of source code: start position, end position *)
type loc0 = (srcpos * srcpos) (* ?loc *)

let dummy_srcpos = ("<nowhere>", 0, 0)
let dummy_loc0 = (dummy_srcpos, dummy_srcpos)

(*
Visual Studio format:
C:\ddd\sss.xyz(123): error VF0001: blah
C:\ddd\sss.xyz(123,456): error VF0001: blah
C:\ddd\sss.xyz(123,456-789): error VF0001: blah
C:\ddd\sss.xyz(123,456-789,123): error VF0001: blah
GNU format:
C:\ddd\sss.xyz:123: error VF0001: blah
C:\ddd\sss.xyz:123.456: error VF0001: blah
C:\ddd\sss.xyz:123.456-789: error VF0001: blah
C:\ddd\sss.xyz:123.456-789.123: error VF0001: blah
See
http://blogs.msdn.com/msbuild/archive/2006/11/03/msbuild-visual-studio-aware-error-messages-and-message-formats.aspx
and
http://www.gnu.org/prep/standards/standards.html#Errors
*)

let string_of_srcpos (p,l,c) = p ^ "(" ^ string_of_int l ^ "," ^ string_of_int c ^ ")"

let string_of_loc0 ((p1, l1, c1), (p2, l2, c2)) =
  p1 ^ "(" ^ string_of_int l1 ^ "," ^ string_of_int c1 ^
  if p1 = p2 then
    if l1 = l2 then
      if c1 = c2 then
        ")"
      else
        "-" ^ string_of_int c2 ^ ")"
    else
      "-" ^ string_of_int l2 ^ "," ^ string_of_int c2 ^ ")"
  else
    ")-" ^ p2 ^ "(" ^ string_of_int l2 ^ "," ^ string_of_int c2 ^ ")"

(* A token provenance. Complex because of the C preprocessor. *)

type loc =
  Lexed of loc0
| DummyLoc
| MacroExpansion of
    loc (* Call site *)
    * loc (* Body token *)
| MacroParamExpansion of
    loc (* Parameter occurrence being expanded *)
    * loc (* Argument token *)
 
let dummy_loc = DummyLoc

type quick_fix_kind =
  InsertTextAt of srcpos * string

type error_attribute =
  HelpTopic of string
| QuickFix of string (* brief description *) * quick_fix_kind

exception StaticError of loc * string * error_attribute list option

let static_error l msg url =
  let attrs =
    match url with
      None -> None
    | Some url -> Some [HelpTopic url]
  in
  raise (StaticError (l, msg, attrs))

type error_attributes = {help_topic: string option; quick_fixes: (string * quick_fix_kind) list}

let parse_error_attributes attrs =
  let rec parse topic fixes = function
    | [] -> {help_topic = topic; quick_fixes = fixes}
    | HelpTopic url::rest -> parse (Some url) fixes rest
    | QuickFix (desc, fixKind)::rest -> parse topic ((desc, fixKind)::fixes) rest
  in
  match attrs with
    None -> {help_topic = None; quick_fixes = []}
  | Some attrs -> parse None [] attrs

let rec root_caller_token l =
  match l with
    Lexed l -> l
  | DummyLoc -> dummy_loc0
  | MacroExpansion (lcall, _) -> root_caller_token lcall
  | MacroParamExpansion (lparam, _) -> root_caller_token lparam

let rec lexed_loc l =
  match l with
    Lexed l -> l
  | DummyLoc -> dummy_loc0
  | MacroExpansion (lcall, lbodyTok) -> lexed_loc lbodyTok
  | MacroParamExpansion (lparam, largTok) -> lexed_loc largTok

let rec string_of_loc l =
  match l with
    Lexed l0 -> string_of_loc0 l0
  | DummyLoc -> "<dummy location>"
  | MacroExpansion (lcall, lbody) -> Printf.sprintf "%s (body token %s)" (string_of_loc lcall) (string_of_loc lbody)
  | MacroParamExpansion (lparam, larg) -> Printf.sprintf "%s (argument token %s)" (string_of_loc lparam) (string_of_loc larg)

exception NotAConstant

(* Region: ASTs *)

(* Because using "True" and "False" for everything results in unreadable sourcecode *)
type inductiveness = (* ? inductiveness *)
  | Inductiveness_Inductive (* prefixing to avoid nameclash with "Inductive" *)
  | Inductiveness_CoInductive

let string_of_inductiveness inductiveness =
  match inductiveness with
  | Inductiveness_Inductive -> "inductive"
  | Inductiveness_CoInductive -> "coinductive"
  
type signedness = Signed | Unsigned

type int_bitwidth =
  LitWidth of int
| IntWidth
| LongWidth
| PtrWidth

type int_rank =
| CharRank
| ShortRank
| IntRank
| LongRank
| LongLongRank
| PtrRank
| FixedWidthRank of int  (* The size of an integer of rank k is 2^k bytes. *)

type rust_ref_kind =
  Mutable
| Shared

type type_ = (* ?type_ *)
    Bool
  | Void
  | Int of signedness * int_rank
  | RustChar
  | RealType  (* Mathematical real numbers. Used for fractional permission coefficients. Also used for reasoning about floating-point code. *)
  | Float
  | Double
  | LongDouble
  | StructType of string * type_ list
  | UnionType of string
  | PtrType of type_
  | RustRefType of type_ (*lifetime*) * rust_ref_kind * type_
  | FuncType of string   (* The name of a typedef whose body is a C function type. *)
  | InlineFuncType of type_ (* InlineFuncType rt denotes Rust type 'unsafe fn(...) -> rt'. *)
  | InductiveType of string * type_ list
  | PredType of string list * type_ list * int option * inductiveness (* if None, not necessarily precise; if Some n, precise with n input parameters *)
  | PureFuncType of type_ * type_  (* Curried *)
  | ObjType of string * type_ list (* type arguments *)
  | ArrayType of type_
  | StaticArrayType of type_ (* element type *) * type_ (* size; in C this is always a LiteralConstType *) (* C array type T[N]; Rust array type [T; N] *)
  | LiteralConstType of int (* Rust const generic argument *)
  | BoxIdType (* box type, for shared boxes *)
  | HandleIdType (* handle type, for shared boxes *)
  | AnyType (* supertype of all inductive datatypes; useful in combination with predicate families *)
  | RealTypeParam of string (* a reference to a type parameter declared in the enclosing Real code *)
  | InferredRealType of string
  | GhostTypeParam of string (* a reference to a type parameter declared in the ghost code *)
  | GhostTypeParamWithEqs of (* a reference to a type parameter declared in the ghost code *)
      string *
      ((string * type_ list * string) * type_) list (* type projection equalities: TraitName<TraitArgs>::AssocTypeName == T *)
  | InferredType of < > * inferred_type_state ref (* inferred type, is unified during type checking. '< >' is the type of objects with no methods. This hack is used to prevent types from incorrectly comparing equal, as in InferredType (ref Unconstrained) = InferredType (ref Unconstrained). Yes, ref Unconstrained = ref Unconstrained. But object end <> object end. *)
  | ClassOrInterfaceName of string (* not a real type; used only during type checking *)
  | PackageName of string (* not a real type; used only during type checking *)
  | RefType of type_ (* not a real type; used only for locals whose address is taken *)
  | AbstractType of string
  | StaticLifetime (* 'static in Rust *)
  | ProjectionType of type_ * string (* trait name *) * type_ list (* trait generic args *) * string (* associated type name *) (* In Rust: <T as X<GArgs>>::Y *)
and inferred_type_state =
    Unconstrained
  | ContainsAnyConstraint of bool (* allow the type to contain 'any' in positive positions *)
  | EqConstraint of type_

let type_fold_open state f = function
  Bool | Void | Int (_, _) | RustChar | RealType | Float | Double | LongDouble -> state
| StructType (sn, targs) -> List.fold_left f state targs
| UnionType _ -> state
| PtrType tp -> f state tp
| RustRefType (lft, _, tp) -> f (f state lft) tp
| FuncType _ -> state
| InlineFuncType tp -> f state tp
| InductiveType (i, targs) -> List.fold_left f state targs
| PredType (tparams, targs, _, _) -> List.fold_left f state targs
| PureFuncType (tp1, tp2) -> f (f state tp1) tp2
| ObjType (_, targs) -> List.fold_left f state targs
| ArrayType tp -> f state tp
| StaticArrayType (elem_tp, size) -> f (f state elem_tp) size
| LiteralConstType _ -> state
| BoxIdType | HandleIdType | AnyType | RealTypeParam _ | InferredRealType _ | GhostTypeParam _ | InferredType (_, _) | ClassOrInterfaceName _ | PackageName _ -> state
| RefType tp -> f state tp
| AbstractType _ | StaticLifetime -> state
| GhostTypeParamWithEqs (tp, eqs) -> List.fold_left (fun state (_, tp) -> f state tp) state eqs
| ProjectionType (tp, _, targs, _) -> List.fold_left f (f state tp) targs

let is_ptr_type tp =
  match tp with
    PtrType _ -> true
  | _ -> false

let inferred_type_constraint_le c1 c2 =
  match c1, c2 with
    _, Unconstrained -> true
  | Unconstrained, _ -> false
  | _, ContainsAnyConstraint true -> true
  | ContainsAnyConstraint true, _ -> false
  | ContainsAnyConstraint false, ContainsAnyConstraint false -> true

let inferred_type_constraint_meet c1 c2 =
  if inferred_type_constraint_le c1 c2 then c1 else c2

type integer_limits = {max_unsigned_big_int: big_int; min_signed_big_int: big_int; max_signed_big_int: big_int}

let max_width = 4 (* (u)int128 *)

let integer_limits_table =
  Array.init (max_width + 1) begin fun k ->
    let max_unsigned_big_int = pred_big_int (shift_left_big_int unit_big_int (8 * (1 lsl k))) in
    let max_signed_big_int = shift_right_big_int max_unsigned_big_int 1 in
    let min_signed_big_int = pred_big_int (minus_big_int max_signed_big_int) in
    {max_unsigned_big_int; max_signed_big_int; min_signed_big_int}
  end

let max_unsigned_big_int k = integer_limits_table.(k).max_unsigned_big_int
let min_signed_big_int k = integer_limits_table.(k).min_signed_big_int
let max_signed_big_int k = integer_limits_table.(k).max_signed_big_int

type data_model = {int_width: int; long_width: int; ptr_width: int}
let data_model_32bit = {int_width=2; long_width=2; ptr_width=2}
let data_model_java = {int_width=2; long_width=3; ptr_width=3 (*arbitrary value; ptr_width is not relevant to Java programs*)}
let data_model_lp64 = {int_width=2; long_width=3; ptr_width=3}
let data_model_llp64 = {int_width=2; long_width=2; ptr_width=3}
let data_model_ip16 = {int_width=1; long_width=2; ptr_width=1}
let data_model_i16 = {int_width=1; long_width=2; ptr_width=2}
let data_models_ = [
  "IP16", data_model_ip16;
  "I16", data_model_i16;
  "32bit/ILP32", data_model_32bit;
  "Win64/LLP64", data_model_llp64;
  "Linux64/macOS/LP64", data_model_lp64
]
let data_models = [
  "IP16", data_model_ip16;
  "I16", data_model_i16;
  "ILP32", data_model_32bit;
  "32bit", data_model_32bit;
  "LLP64", data_model_llp64;
  "Win64", data_model_llp64;
  "LP64", data_model_lp64;
  "Unix64", data_model_lp64;
  "Linux64", data_model_lp64;
  "OSX", data_model_lp64;
  "macOS", data_model_lp64
]
let data_model_of_string s =
  let s = String.uppercase_ascii s in
  match head_flatmap_option (fun (k, v) -> if String.uppercase_ascii k = s then Some v else None) data_models with
    None -> failwith ("Data model must be one of " ^ String.concat ", " (List.map fst data_models))
  | Some v -> v
let string_of_data_model data_model =
  match Util.flatmap (fun (name, model) -> if model = data_model then [name] else []) data_models with
    name::_ -> name
  | [] -> "(unnamed)"
let intmax_width = 3 (* Assume that sizeof(intmax_t) is always 8 *)

let java_byte_type = Int (Signed, FixedWidthRank 0)
let java_short_type = Int (Signed, ShortRank)
let java_char_type = Int (Unsigned, FixedWidthRank 1)
let java_int_type = Int (Signed, IntRank)
let java_long_type = Int (Signed, LongRank)

let is_arithmetic_type t =
  match t with
    Int (_, _)|RealType|Float|Double|LongDouble -> true
  | _ -> false

let is_inductive_type t =
  (match t with
  | InductiveType _ -> true
  | _ -> false
  )

type prover_type = ProverInt | ProverBool | ProverReal | ProverInductive (* ?prover_type *)

type pred_name = PredFam of string | PredCtor of string | LocalVar of string

class predref (name: pred_name) (domain: type_ list) (inputParamCount: int option) = (* ?predref *)
  object
    method name = name
    method domain = domain
    method inputParamCount = inputParamCount
    method is_precise = match inputParamCount with None -> false | Some _ -> true 
  end

type
  ident_scope = (* ?ident_scope *)
    LocalVar
  | FuncName
  | PredFamName
  | EnumElemName of big_int
  | GlobalName
  | ModuleName
  | PureFuncName of type_ list (* Type arguments for type parameters that carry a typeid *)
  | ClassOrInterfaceNameScope
  | PackageNameScope

type int_literal_lsuffix = NoLSuffix | LSuffix | LLSuffix

type float_literal_suffix = FloatFSuffix | FloatLSuffix

type pointsto_kind = RegularPointsTo | MaybeUninit

type assignment_kind =
  Mutation
| Initialization (* Generated by the MIR translator for MIR assignments to non-`mut` locals. *)

(** Types as they appear in source code, before validity checking and resolution. *)
type type_expr = (* ?type_expr *)
    StructTypeExpr of loc * string option * (string list (* type parameters *) * field list) option * struct_attr list * type_expr list (* type arguments *)
  | UnionTypeExpr of loc * string option * field list option
  | EnumTypeExpr of loc * string option * (string * expr option) list option
  | PtrTypeExpr of loc * type_expr
  | RustRefTypeExpr of loc * type_expr * rust_ref_kind * type_expr
  | ArrayTypeExpr of loc * type_expr
  | StaticArrayTypeExpr of loc * type_expr (* type *) * type_expr (* number of elements; in C this is always a LiteralConstTypeExpr *)
  | LiteralConstTypeExpr of loc * int
  | FuncTypeExpr of loc * type_expr (* return type *) * (type_expr * string) list (* parameters *)
  | ManifestTypeExpr of loc * type_  (* A type expression that is obviously a given type. *)
  | IdentTypeExpr of loc * string option (* package name *) * string
  | ConstructedTypeExpr of loc * string * type_expr list  (* A type of the form x<T1, T2, ...> *)
  | PredTypeExpr of loc * type_expr list * int option (* if None, not necessarily precise; if Some n, precise with n input parameters *)
  | PureFuncTypeExpr of loc * (type_expr * (loc * string) option) list * expr (* 'requires' clause *) option   (* Potentially uncurried *)
  | LValueRefTypeExpr of loc * type_expr
  | ConstTypeExpr of loc * type_expr
  | ProjectionTypeExpr of loc * type_expr * string (* trait name *) * type_expr list (* trait generic args *) * string (* associated type name *) (* In Rust: <T as X<GArgs>>::Y *)
and
  operator =  (* ?operator *)
  | Add | Sub | PtrDiff | Le | Ge | Lt | Gt | Eq | Neq | And | Or | Xor | Not | Mul | Div | Mod | BitNot | BitAnd | BitXor | BitOr | ShiftLeft | ShiftRight
  | MinValue of type_ | MaxValue of type_
and
  expr = (* ?expr *)
    True of loc
  | False of loc
  | Null of loc
  | Var of loc * string
  | WVar of loc * string * ident_scope
  | TruncatingExpr of loc * expr
  | Operation of (* voor operaties met bovenstaande operators*)
      loc *
      operator *
      expr list
  | WOperation of (* see [woperation_result_type] *)
      loc *
      operator *
      expr list *
      type_
      (* The type of the first operand, after promotion and the usual arithmetic conversions.
         For all operators except the pointer offset and bitwise shift operators, this is also the type of the second operand, if any.
         For the pointer offset operators (Add and Sub where the first operand is a pointer) the second operand is of integral type.
         For all operators except the relational ones (whose result type is bool) and PtrDiff (whose result type is ptrdiff_t), this is also the type of the result.
         Used to select the right semantics (e.g. Real vs. Int vs. Bool) and for overflow checking.
         (Floating-point operations are turned into function calls by the type checker and do not appear as WOperation nodes.)
         If the operands have narrower types before promotion and conversion, they will be of the form Upcast (_, _, _). *)
  | IntLit of loc * big_int * bool (* decimal *) * bool (* U suffix *) * int_literal_lsuffix   (* int literal*)
  | WIntLit of loc * big_int
  | RealLit of loc * num * float_literal_suffix option
  | StringLit of loc * string (* string literal *)
  | ClassLit of loc * string (* class literal in java *)
  | Typeid of loc * expr
  | TypeInfo of loc * type_
  | Read of loc * expr * string
  | Select of loc * expr * string (* reading a field in C; Java uses Read *)
  | ActivatingRead of loc * expr * string (* activates the union member *)
  | ArrayLengthExpr of loc * expr
  (* Expression which returns the value of a field of an object *)
  | WRead of
      loc *
      expr *
      string (* parent *) *
      string list (* type parameters *) *
      string (* field name *) *
      type_ (* range, before instantiation of type parameters *) *
      type_ list (* type arguments *) *
      bool (* static *) *
      constant_value option option ref *
      ghostness
  | WReadUnionMember of
      loc *
      expr *
      string (* parent *) *
      int * (* member index *)
      string (* member name *) *
      type_ (* range *) *
      bool (* activates the member *)
  (* Expression which returns the value of a field of
   * a struct that is not an object - only for C *)
  | WSelect of
      loc *
      expr *
      string (* parent *) *
      string list * (* type parameters *)
      string (* field name *) *
      type_ (* range type, before instantiation of type parameters *) *
      type_ list (* type arguments *)
  (* Expression which returns the value of a field of an instance of an
   * inductive data type. *)
  | WReadInductiveField of
      loc *
      expr (* The expression which results an instance of the inductive
            * data type. (usually just a variable) *) *
      string (* inductive data type name *) *
      string (* constructor name *) *
      string (* field name *) *
      type_ list (* type arguments *) *
      type_ (* uninstantiated field type *) *
      type_ (* instantiated field type *)
  | ReadArray of loc * expr * expr
  | WReadArray of loc * expr * type_ * expr
  | Deref of (* pointer dereference *)
      loc *
      expr
  | WDeref of
      loc *
      expr *
      type_ (* pointee type *)
  | CallExpr of (* oproep van functie/methode/lemma/fixpoint *)
      loc *
      string *
      type_expr list (* type arguments *) *
      pat list (* indices, in case this is really a predicate assertion *) *
      pat list (* arguments *) *
      method_binding
  | ExprCallExpr of (* Call whose callee is an expression instead of a plain identifier *)
      loc *
      expr *
      pat list
  | WFunPtrCall of loc * expr * string option (* function type name *) * expr list
  | WPureFunCall of loc * string * type_ list * expr list
  | WPureFunValueCall of loc * expr * expr list
  | WFunCall of loc * string * type_ list * expr list * method_binding
  | WMethodCall of
      loc *
      string (* declaring class or interface *) *
      string (* method name *) *
      type_ list (* parameter types (not including receiver) *) *
      expr list (* args, including receiver if instance method *) *
      method_binding *
      (string * type_ ) list (* type param environment *)
  | NewArray of loc * type_expr * expr
  (* If type arguments are None -> regular object creation or raw objects. [] -> type inference required and if the list is populated: parameterised type creation *)
  | NewObject of loc * string * expr list * type_expr list option
  | CxxConstruct of 
      loc *
      string * (* constructor mangled name *)
      type_expr * (* type of object that will be constructed *)
      expr list (* args passed to constructor *)
  | WCxxConstruct of 
      loc *
      string *
      type_ *
      expr list
  | CxxNew of
      loc *
      type_expr *
      expr option (* construct expression *)
  | WCxxNew of
      loc * 
      type_ * 
      expr option
  | CxxDelete of
      loc *
      expr
  | NewArrayWithInitializer of loc * type_expr * expr list 
  | IfExpr of loc * expr * expr * expr
  | SwitchExpr of
      loc *
      expr *
      switch_expr_clause list *
      (loc * expr) option (* default clause *)
  | WSwitchExpr of
      loc *
      expr *
      string * (* inductive type, fully qualified *)
      type_ list * (* type arguments *)
      switch_expr_clause list *
      (loc * expr) option * (* default clause *)
      (string * type_) list * (* type environment *)
      type_ (* result type *)
  | PredNameExpr of loc * string (* naam van predicaat en line of code*)
  | CastExpr of loc * type_expr * expr (* cast *)
  | CxxLValueToRValue of loc * expr
  | CxxDerivedToBase of loc * expr * type_expr
  | Upcast of expr * type_ (* from *) * type_ (* to *)  (* Not generated by the parser; inserted by the typechecker. Required to prevent bad downcasts during autoclose. *)
  | TypedExpr of expr * type_  (* Not generated by the parser. In 'TypedExpr (e, t)', 't' should be the type of 'e'. Allows typechecked expression 'e' to be used where a not-yet-typechecked expression is expected. *)
  | WidenedParameterArgument of expr (* Appears only as part of LitPat (WidenedParameterArgument e). Indicates that the predicate parameter is considered to range over a larger set (e.g. Object instead of class C). *)
  | SizeofExpr of loc * expr
  | AlignofExpr of loc * type_expr
  | TypeExpr of type_expr (* Used to represent the E in 'sizeof E' when E is of the form '( T )' where T is a type *)
  | GenericExpr of loc * expr * (type_expr * expr) list * expr option (* default clause *) (* C11 generic selection (keyword '_Generic') *)
  | AddressOf of loc * expr
  | ProverTypeConversion of prover_type * prover_type * expr  (* Generated during type checking in the presence of type parameters, to get the prover types right *)
  | Unbox of expr * type_ (* Generated during type checking; Unbox (e, t) converts the value of e, which is of prover type Inductive, to the prover type of t *)
  | ArrayTypeExpr' of loc * expr (* horrible hack --- for well-formed programs, this exists only during parsing *)
  | AssignExpr of loc * expr * assignment_kind * expr
  | AssignOpExpr of loc * expr * operator * expr * bool (* true = return value of lhs before operation *)
  | WAssignOpExpr of loc * expr * string * expr * bool
    (* Semantics of [WAssignOpExpr (l, lhs, x, rhs, postOp)]:
       1. Evaluate [lhs] to an lvalue L
       2. Get the value of L, call it v
       3. Evaluate [rhs] with x bound to v to an rvalue V
       4. Assign V to L
       5. Return (postOp ? v : V)
    *)
  | CommaExpr of loc * expr * expr
  | InstanceOfExpr of loc * expr * type_expr
  | SuperMethodCall of loc * string * expr list
  | WSuperMethodCall of loc * string (*superclass*) * string * expr list * (loc * ghostness * (type_ option) * (string * type_) list * asn * asn * (type_ * asn) list * bool (*terminates*) * int (*rank*) option * visibility)
  | InitializerList of loc * ((loc * string (* field name *)) option * expr) list
  | SliceExpr of loc * pat option * pat option
  | PointsTo of
        loc *
        expr *
        pointsto_kind *
        pat
  | WPointsTo of
      loc *
      expr *
      type_ *
      pointsto_kind *
      pat
  | PredAsn of (* Predicate assertion, before type checking *)
      loc *
      string *
      type_expr list *
      pat list (* indices of predicate family instance *) *
      pat list *
      method_binding
  | WPredAsn of (* Predicate assertion, after type checking. (W is for well-formed) *)
      loc *
      predref *
      bool * (* prefref refers to global name *)
      type_ list *
      pat list *
      pat list
  | PredExprAsn of
      loc *
      expr *
      pat list
  | WPredExprAsn of
      loc *
      expr *
      type_ list * (* parameter types *)
      int option * (* inputParamCount *)
      pat list
  | InstPredAsn of
      loc *
      expr *
      string *
      expr * (* index *)
      pat list
  | WInstPredAsn of
      loc *
      expr option *
      string (* static type *) *
      class_finality (* finality of static type *) *
      string (* family type *) *
      string *
      expr (* index *) *
      pat list
  | ExprAsn of (* uitdrukking regel-expr *)
      loc *
      expr
  | Sep of (* separating conjunction *)
      loc *
      asn *
      asn
  | IfAsn of (* if-predicate in de vorm expr? p1:p2 regel-expr-p1-p2 *)
      loc *
      expr *
      asn *
      asn
  | WSwitchAsn of (* switch over cons van inductive type regel-expr-clauses*)
      loc *
      expr *
      string * (* inductive type (fully qualified) *)
      wswitch_asn_clause list
  | EmpAsn of  (* als "emp" bij requires/ensures staat -regel-*)
      loc
  | ForallAsn of 
      loc *
      type_expr *
      string *
      expr
  | CoefAsn of (* fractional permission met coeff-predicate*)
      loc *
      pat *
      asn
  | EnsuresAsn of loc * string (* result variable *) * asn
  | MatchAsn of loc * expr * pat
  | WMatchAsn of loc * expr * pat * type_
  | LetTypeAsn of loc * string * type_ * asn (* `let_type U = T in A` means A with type T substituted for type parameter U *)
  | TypePredExpr of loc * type_expr * string
  | WTypePredExpr of loc * type_ * string
and
  asn = expr
and
  pat = (* ?pat *)
    LitPat of expr (* literal pattern *)
  | VarPat of loc * string (* var pattern, aangeduid met ? in code *)
  | DummyPat (*dummy pattern, aangeduid met _ in code *)
  | DummyVarPat (* '? _' *)
  | CtorPat of loc * string * pat list
  | WCtorPat of loc * string * type_ list * string * type_ list * type_ list * pat list * expr option (* The expression if it is also a literal pattern *)
and
  wswitch_asn_clause = (* ?switch_asn_clause *)
  | WSwitchAsnClause of
      loc * 
      string (* ctor name *) *
      string (* full ctor name *) *
      string option list (* pattern variables, or None if _ *) *
      prover_type option list (* Boxing info *) *
      asn
and
  switch_expr_clause = (* ?switch_expr_clause *)
    SwitchExprClause of
      loc *
      string (* constructor name *) *
      string list (* argument names *) *
      expr (* body *)
and
  language = (* ?language *)
    Java
  | CLang
and
  dialect = (* ?dialect *)
    | Cxx
    | Rust
and
  method_binding = (* ?method_binding *)
    Static
  | Instance
  | PredFamCall
  | PredCtorCall
  | LocalVarPredCall
and
  visibility = (* ?visibility *)
    Public
  | Protected
  | Private
  | Package
and
  package = (* ?package *)
    PackageDecl of loc * string * import list * decl list
and
  import = (* ?import *)
    Import of
        loc *
        ghostness *
        string *
        string option (* None betekent heel package, Some string betekent 1 ding eruit *)
and 
  producing_handle_predicate =
    ConditionalProducingHandlePredicate of loc * expr (* condition *) * string (* handle name *) * (expr list) (* args *) * producing_handle_predicate
  | BasicProducingHandlePredicate of loc * string (* handle name *) * (expr list) (* args *)
and
  consuming_handle_predicate = 
    ConsumingHandlePredicate of loc * string * (pat list)
and
  stmt = (* ?stmt *)
    PureStmt of (* Statement of the form /*@ ... @*/ *)
        loc *
        stmt
  | NonpureStmt of (* Nested non-pure statement; used for perform_action statements on shared boxes. *)
      loc *
      bool (* allowed *) *
      stmt
  | DeclStmt of (* enkel declaratie *)
      loc *
      (loc * type_expr option * string * expr option * (bool ref (* indicates whether address is taken *) * (string * bool (*is_const_var*)) list ref option ref (* pointer to enclosing block's list of variables whose address is taken *))) list
  | ExprStmt of expr
  | IfStmt of (* if  regel-conditie-branch1-branch2  *)
      loc *
      expr *
      stmt list *
      stmt list
  | SwitchStmt of (* switch over inductief type regel-expr- constructor)*)
      loc *
      expr *
      switch_stmt_clause list
  | Assert of loc * asn (* assert regel-predicate *)
  | Leak of loc * asn (* expliciet lekken van assertie, nuttig op einde van thread*)
  | Open of
      loc *
      expr option *  (* Target object *)
      string *
      type_expr list *  (* Type arguments *)
      pat list *  (* Indices for predicate family instance, or constructor arguments for predicate constructor *)
      pat list *  (* Arguments *)
      pat option  (* Coefficient for fractional permission *)
  | Close of
      loc *
      expr option *
      string *
      type_expr list *
      pat list *
      pat list *
      pat option
  | ReturnStmt of loc * expr option (*return regel-return value (optie) *)
  | WhileStmt of
      loc *
      expr *
      loop_spec option *
      expr option * (* decreases clause *)
      stmt list * (* body *)
      stmt list (* statements to be executed after the body: for increment or do-while condition check. 'continue' jumps here. *)
  | BlockStmt of
      loc *
      decl list *
      stmt list *
      loc *
      (string * bool (*is_const_var*)) list ref
  | PerformActionStmt of
      loc *
      bool ref (* in non-pure context *) *
      string *
      pat list *
      consuming_handle_predicate list *
      loc *
      string *
      expr list *
      stmt list *
      loc (* close brace of body *) *
      (loc * expr list) option *
      (bool (* indicates whether a fresh handle id should be generated *) * producing_handle_predicate) list
      (*loc *
      string *
      expr list*)
  | SplitFractionStmt of (* split_fraction ... by ... *)
      loc *
      string *
      type_expr list *
      pat list *
      expr option
  | MergeFractionsStmt of (* merge_fraction ...*)
      loc *
      asn
  | CreateBoxStmt of
      loc *
      string *
      string *
      expr list *
      expr list * (* lower bounds *)
      expr list * (* upper bounds *)
      (loc * string * bool (* indicates whether an is_handle chunk is generated *) * string * expr list) list (* and_handle clauses *)
  | CreateHandleStmt of
      loc *
      string *
      bool * (* indicates whether an is_handle chunk is generated *)
      string *
      expr
  | DisposeBoxStmt of
      loc *
      string *
      pat list *
      (loc * string * pat list) list (* and_handle clauses *)
  | LabelStmt of loc * string
  | GotoStmt of loc * string
  | NoopStmt of loc
  | InvariantStmt of
      loc *
      asn (* join point *)
  | SpecStmt of
      loc *
      asn * (* requires clause*)
      asn (* ensures clause *)
  | ProduceLemmaFunctionPointerChunkStmt of
      loc *
      expr option *
      (string * type_expr list * expr list * (loc * string) list * loc * stmt list * loc) option *
      stmt option
  | DuplicateLemmaFunctionPointerChunkStmt of
      loc *
      expr
  | ProduceFunctionPointerChunkStmt of
      loc *
      string * (* name of function typedef *)
      expr * (* function pointer expression *)
      type_expr list * (* type argument *)
      expr list *
      (loc * string) list *
      loc *
      stmt list *
      loc
  | Throw of loc * expr
  | TryCatch of
      loc *
      stmt list *
      (loc * type_expr * string * stmt list) list
  | TryFinally of
      loc *
      stmt list *
      loc *
      stmt list
  | Break of loc
  | Continue of loc
  | SuperConstructorCall of loc * expr list
and
  loop_spec = (* ?loop_spec *)
  | LoopInv of asn
  | LoopSpec of asn * asn
and
  switch_stmt_clause = (* ?switch_stmt_clause *)
  | SwitchStmtClause of loc * expr * stmt list
  | SwitchStmtDefaultClause of loc * stmt list
and
  func_kind = (* ?func_kind *)
  | Regular
  | Fixpoint
  | Lemma of bool (* indicates whether an axiom should be generated for this lemma *) * expr option (* trigger *)
and
  meth = (* ?meth *)
  | Meth of
      loc * 
      ghostness * 
      type_expr option * 
      string * 
      (type_expr * string) list * 
      (asn * asn * ((type_expr * asn) list) * bool (*terminates*) ) option * 
      ((stmt list * loc (* Close brace *)) * int (*rank*)) option * 
      method_binding * 
      visibility *
      bool * (* is declared abstract? *)
      string list (* tparams *)
and
  cons = (* ?cons *)
  | Cons of
      loc * 
      (type_expr * string) list * 
      (asn * asn * ((type_expr * asn) list) * bool (*terminates*) ) option * 
      ((stmt list * loc (* Close brace *)) * int (*rank*)) option * 
      visibility
and
  instance_pred_decl = (* ?instance_pred_decl *)
  | InstancePredDecl of loc * string * (type_expr * string) list * asn option
and
  class_finality =
  | FinalClass
  | ExtensibleClass
and
  decl = (* ?decl *)
    Struct of 
      loc * 
      string *
      string list * (* type parameters *) 
      (base_spec list * field list * instance_pred_decl list * bool (* is polymorphic *)) option *
      struct_attr list
  | Union of loc * string * field list option
  | Inductive of  (* inductief data type regel-naam-type parameters-lijst van constructors*)
      loc *
      string *
      string list * (*tparams*)
      ctor list
  | AbstractTypeDecl of loc * string
  | Class of
      loc *
      bool (* abstract *) *
      class_finality *
      string * (* class name *)
      meth list *
      field list *
      cons list *
      (string * type_expr list) (* superclass with targs *) *
      string list (* type parameters *) *
      (string * type_expr list) list (* itfs with targs *) *
      instance_pred_decl list
  | Interface of 
      loc *
      string *
      (string * type_expr list) list * (* interfaces *)
      field list *
      meth list *
      string list * (* type parameters *) 
      instance_pred_decl list
  | PredFamilyDecl of
      loc *
      string *
      string list (* type parameters *) *
      int (* number of indices *) *
      type_expr list *
      int option (* (Some n) means the predicate is precise and the first n parameters are input parameters *) *
      inductiveness
  | PredFamilyInstanceDecl of
      loc *
      string *
      string list (* type parameters *) *
      (loc * string) list *
      (type_expr * string) list *
      asn
  | PredCtorDecl of
      loc *
      string *
      string list (* type parameters *) *
      (type_expr * string) list *
      (type_expr * string) list *
      int option * (* (Some n) means the predicate is precise and the first n parameters are input parameters *)
      asn
  | Func of
      loc *
      func_kind *
      string list *  (* type parameters *)
      type_expr option *  (* return type *)
      string *  (* name *)
      (type_expr * string) list *  (* parameters *)
      bool (* nonghost_callers_only *) *
      (
        (string * type_expr list * (loc * string) list) option (* implemented function type, with function type type arguments and function type arguments *) *
        (loc * stmt list) option (* prototype implementation proof *)
      ) *
      (asn * (string (* result variable *) * asn)) option *  (* contract *)
      bool *  (* terminates *)
      (stmt list * loc (* Close brace *)) option *  (* body *)
      bool * (* virtual *)
      (string list) (* overrides *)
  | CxxCtor of 
      loc *
      string * (* mangled name *)
      (type_expr * string) list * (* params *)
      (asn * asn) option * (* pre post *)
      bool * (* terminates *)
      ((string * (expr * bool (* is written *)) option) list (* init list *) * (stmt list * loc (* close brace *))) option *
      bool * (* implicit *)
      type_ (* parent type *)
  | CxxDtor of 
      loc *
      string * (* mangled_name *)
      (asn * asn) option * (* pre post *)
      bool * (* terminates *)
      (stmt list * loc (* close brace *)) option *
      bool * (* implicit *)
      type_ * (* parent type *)
      bool * (* virtual *)
      string list (* overrides *)
  (** Do not confuse with FuncTypeDecl *)
  | TypedefDecl of
      loc *
      type_expr *
      string *
      string list (* type parameters *)
      
  (** Used for declaring a function type like "typedef void myfunc();"
    * or "typedef lemma ..."
    *)
  | FuncTypeDecl of
      loc *
      ghostness * (* e.g. a "typedef lemma" is ghost. *)
      type_expr option * (* return type *)
      string *
      string list * (* type parameters *)
      (type_expr * string) list *
      (type_expr * string) list *
      (asn * (string (* result variable *) * asn) * bool) (* precondition, postcondition, terminates *)
  | BoxClassDecl of
      loc *
      string *
      (type_expr * string) list *
      asn *
      action_decl list *
      handle_pred_decl list
  (* enum def met line - name - elements *)
  | EnumDecl of loc * string * (string * expr option) list
  | Global of loc * type_expr * string * expr option
  | UnloadableModuleDecl of loc
  | ImportModuleDecl of loc * string
  | RequireModuleDecl of loc * string
  | ModuleDecl of loc * string * import list * decl list (* A Rust module. Is flattened into a list of PackageDecl after parsing. *)
  | TypePredDecl of loc * type_expr * string * string
  | TypePredDef of loc * string list * type_expr * string * (loc * string, string list * int option * asn) Either.t
  | TypeWithTypeidDecl of (* introduce a local type name whose typeid is given by the expression *)
      loc *
      string *
      expr
  | FuncSpecializationDecl of (* A function specialization declaration, used to declare a specialization of a function for a specific type. *)
      loc *
      string * (* name of the generic function, e.g. "std::iter::IntoIterator::into_iter" *)
      bool * (* the name of the generic function is relative to the current package *)
      string (* name of the specialized function, e.g. "std::ops::<Range<usize> as std::iter::IntoIterator>::into_iter" *) *
      string list (* type parameters of the specialized function *) *
      type_expr list (* type arguments for the generic function, e.g. Range<usize> *)
and (* shared box is deeltje ghost state, waarde kan enkel via actions gewijzigd worden, handle predicates geven info over de ghost state, zelfs als er geen eigendom over de box is*)
  action_decl = (* ?action_decl *)
  | ActionDecl of loc * string * bool (* does performing this action require a corresponding action permission? *) * (type_expr * string) list * expr * expr
and (* action, kan value van shared box wijzigen*)
  handle_pred_decl = (* ?handle_pred_decl *)
  | HandlePredDecl of loc * string * (type_expr * string) list * string option (* extends *) * asn * preserved_by_clause list
and (* handle predicate geeft info over ghost state van shared box, zelfs als er geen volledige eigendom is vd box*)
  preserved_by_clause = (* ?preserved_by_clause *)
  | PreservedByClause of loc * string * string list * stmt list
and
  ghostness = (* ?ghostness *)
  | Ghost
  | Real
and
  field =
  | Field of (* ?field *)
      loc *
      ghostness *
      type_expr *
      string (* name of the field *) *
      method_binding *
      visibility *
      bool (* final *) *
      expr option
and 
  base_spec =
  | CxxBaseSpec of
      loc * 
      string * (* record name *)
      bool (* virtual *)
and
  ctor = (* ?ctor *)
  | Ctor of
    loc *
    string * (* name of the constructor *)
    (string * type_expr) list (* name and type-expression of the arguments *)
    
and
  member = (* ?member *)
  | FieldMember of field list
  | MethMember of meth
  | ConsMember of cons
  | PredMember of instance_pred_decl
and
  struct_attr =
  | Packed
  | ReprC
and constant_value = (* ?constant_value *)
  IntConst of big_int
| BoolConst of bool
| StringConst of string
| NullConst
| GhostConst of expr

let func_kind_of_ghostness gh =
  match gh with
    Real -> Regular
  | Ghost -> Lemma (false, None)
  
(* Region: some AST inspector functions *)

let type_expr_loc t =
  match t with
    ManifestTypeExpr (l, t) -> l
  | StructTypeExpr (l, sn, _, _, _) -> l
  | UnionTypeExpr (l, un, _) -> l
  | IdentTypeExpr (l, _, x) -> l
  | ConstructedTypeExpr (l, x, targs) -> l
  | PtrTypeExpr (l, te) -> l
  | RustRefTypeExpr (l, _, _, _) -> l
  | ArrayTypeExpr(l, te) -> l
  | PredTypeExpr(l, te, _) -> l
  | PureFuncTypeExpr (l, tes, _) -> l
  | FuncTypeExpr (l, _, _) -> l
  | ConstTypeExpr (l, te) -> l
  | ProjectionTypeExpr (l, te, _, _, _) -> l

let string_of_func_kind f=
  match f with
    Lemma(_) -> "lemma"
  | Regular -> "regular"
  | Fixpoint -> "fixpoint"
let tostring f=
  match f with
  Instance -> "instance"
  | Static -> "static"
let rec expr_loc e =
  match e with
    True l -> l
  | False l -> l
  | Null l -> l
  | Var (l, x) | WVar (l, x, _) -> l
  | IntLit (l, n, _, _, _) -> l
  | WIntLit (l, n) -> l
  | RealLit (l, n, _) -> l
  | StringLit (l, s) -> l
  | ClassLit (l, s) -> l
  | TruncatingExpr (l, e) -> l
  | Operation (l, op, es) -> l
  | WOperation (l, op, es, t) -> l
  | SliceExpr (l, p1, p2) -> l
  | Read (l, e, f)
  | ActivatingRead (l, e, f)
  | Select (l, e, f) -> l
  | ArrayLengthExpr (l, e) -> l
  | WSelect (l, _, _, _, _, _, _) -> l
  | WRead (l, _, _, _, _, _, _, _, _, _) -> l
  | WReadUnionMember (l, _, _, _, _, _, _) -> l
  | WReadInductiveField(l, _, _, _, _, _, _, _) -> l
  | ReadArray (l, _, _) -> l
  | WReadArray (l, _, _, _) -> l
  | Deref (l, e) -> l
  | WDeref (l, e, t) -> l
  | CallExpr (l, g, targs, pats0, pats,_) -> l
  | ExprCallExpr (l, e, es) -> l
  | WPureFunCall (l, g, targs, args) -> l
  | WPureFunValueCall (l, e, es) -> l
  | WFunPtrCall (l, g, ftn, args) -> l
  | WFunCall (l, g, targs, args, _) -> l
  | WMethodCall (l, tn, m, pts, args, fb, tparamEnv) -> l
  | NewObject (l, cn, args, targs) -> l
  | NewArray(l, _, _) -> l
  | NewArrayWithInitializer (l, _, _) -> l
  | IfExpr (l, e1, e2, e3) -> l
  | SwitchExpr (l, e, secs, _) -> l
  | WSwitchExpr (l, e, i, targs, secs, cdef, tenv, t0) -> l
  | SizeofExpr (l, e) -> l
  | AlignofExpr (l, te) -> l
  | TypeExpr te -> type_expr_loc te
  | GenericExpr (l, e, cs, d) -> l
  | PredNameExpr (l, g) -> l
  | CastExpr (l, te, e) -> l
  | Upcast (e, fromType, toType) -> expr_loc e
  | TypedExpr (e, t) -> expr_loc e
  | WidenedParameterArgument e -> expr_loc e
  | AddressOf (l, e) -> l
  | ArrayTypeExpr' (l, e) -> l
  | AssignExpr (l, lhs, _, rhs) -> l
  | AssignOpExpr (l, lhs, op, rhs, postOp) -> l
  | WAssignOpExpr (l, lhs, x, rhs, postOp) -> l
  | CommaExpr (l, e1, e2) -> l
  | ProverTypeConversion (t1, t2, e) -> expr_loc e
  | Unbox (e, t) -> expr_loc e
  | InstanceOfExpr(l, e, tp) -> l
  | SuperMethodCall(l, _, _) -> l
  | WSuperMethodCall(l, _, _, _, _) -> l
  | InitializerList (l, _) -> l
  | PointsTo (l, e, kind, rhs) -> l
  | WPointsTo (l, e, tp, kind, rhs) -> l
  | PredAsn (l, g, targs, ies, es, _) -> l
  | WPredAsn (l, g, _, targs, ies, es) -> l
  | PredExprAsn (l, e, pats) -> l
  | WPredExprAsn (l, e, pts, inputParamCount, pats) -> l
  | InstPredAsn (l, e, g, index, pats) -> l
  | WInstPredAsn (l, e_opt, tns, cfin, tn, g, index, pats) -> l
  | ExprAsn (l, e) -> l
  | MatchAsn (l, e, pat) -> l
  | WMatchAsn (l, e, pat, tp) -> l
  | LetTypeAsn (l, x, t, p) -> l
  | TypePredExpr (l, t, x) -> l
  | WTypePredExpr (l, t, x) -> l
  | Sep (l, p1, p2) -> l
  | IfAsn (l, e, p1, p2) -> l
  | WSwitchAsn (l, e, i, sacs) -> l
  | EmpAsn l -> l
  | ForallAsn (l, tp, i, e) -> l
  | CoefAsn (l, coef, body) -> l
  | EnsuresAsn (l, result_var, body) -> l
  | CxxNew (l, _, _)
  | WCxxNew (l, _, _) -> l
  | CxxDelete (l, _) -> l
  | CxxConstruct (l, _, _, _)
  | WCxxConstruct (l, _, _, _) -> l
  | CxxLValueToRValue (l, _) -> l
  | CxxDerivedToBase (l, _, _) -> l
  | Typeid (l, _) -> l
  | TypeInfo (l, _) -> l
let asn_loc a = expr_loc a
  
let stmt_loc s =
  match s with
    PureStmt (l, _) -> l
  | NonpureStmt (l, _, _) -> l
  | ExprStmt e -> expr_loc e
  | DeclStmt (l, _) -> l
  | IfStmt (l, _, _, _) -> l
  | SwitchStmt (l, _, _) -> l
  | Assert (l, _) -> l
  | Leak (l, _) -> l
  | Open (l, _, _, _, _, _, coef) -> l
  | Close (l, _, _, _, _, _, coef) -> l
  | ReturnStmt (l, _) -> l
  | WhileStmt (l, _, _, _, _, _) -> l
  | Throw (l, _) -> l
  | TryCatch (l, _, _) -> l
  | TryFinally (l, _, _, _) -> l
  | BlockStmt (l, ds, ss, _, _) -> l
  | PerformActionStmt (l, _, _, _, _, _, _, _, _, _, _, _) -> l
  | SplitFractionStmt (l, _, _, _, _) -> l
  | MergeFractionsStmt (l, _) -> l
  | CreateBoxStmt (l, _, _, _, _, _, _) -> l
  | CreateHandleStmt (l, _, _, _, _) -> l
  | DisposeBoxStmt (l, _, _, _) -> l
  | LabelStmt (l, _) -> l
  | GotoStmt (l, _) -> l
  | NoopStmt l -> l
  | InvariantStmt (l, _) -> l
  | SpecStmt (l, _, _) -> l
  | ProduceLemmaFunctionPointerChunkStmt (l, _, _, _) -> l
  | DuplicateLemmaFunctionPointerChunkStmt (l, _) -> l
  | ProduceFunctionPointerChunkStmt (l, ftn, fpe, targs, args, params, openBraceLoc, ss, closeBraceLoc) -> l
  | Break (l) -> l
  | Continue l -> l
  | SuperConstructorCall(l, _) -> l

let type_expr_fold_open f state te =
  match te with
    StructTypeExpr (l, sn, body_opt, attrs, targs) -> List.fold_left f state targs
  | UnionTypeExpr (l, un, body_opt) -> state
  | EnumTypeExpr (l, en, body_opt) -> state
  | PtrTypeExpr (l, te) -> f state te
  | RustRefTypeExpr (l, lft, kind, te) -> f (f state lft) te
  | ArrayTypeExpr (l, te) -> f state te
  | StaticArrayTypeExpr (l, elemTp, size) -> f (f state elemTp) size
  | LiteralConstTypeExpr _ -> state
  | FuncTypeExpr (l, retTp, ps) -> List.fold_left f (f state retTp) (List.map fst ps)
  | ManifestTypeExpr (l, tp) -> state
  | IdentTypeExpr (l, pn, x) -> state
  | ConstructedTypeExpr (l, x, targs) -> List.fold_left f state targs
  | PredTypeExpr (l, paramTps, inputParamCount) -> List.fold_left f state paramTps
  | PureFuncTypeExpr (l, tps, _) -> List.fold_left (fun state (tp, _) -> f state tp) state tps
  | LValueRefTypeExpr (l, tp) -> f state tp
  | ConstTypeExpr (l, tp) -> f state tp
  | ProjectionTypeExpr (l, tp, traitName, traitGenericArgs, assocTypeName) -> List.fold_left f (f state tp) traitGenericArgs

let stmt_fold_open f state s =
  match s with
    PureStmt (l, s) -> f state s
  | NonpureStmt (l, _, s) -> f state s
  | IfStmt (l, _, sst, ssf) -> let state = List.fold_left f state sst in List.fold_left f state ssf
  | SwitchStmt (l, _, cs) ->
    let rec iter state c =
      match c with
        SwitchStmtClause (l, e, ss) -> List.fold_left f state ss
      | SwitchStmtDefaultClause (l, ss) -> List.fold_left f state ss
    in
    List.fold_left iter state cs
  | WhileStmt (l, _, _, _, ss, final_ss) -> let state = List.fold_left f state ss in List.fold_left f state final_ss
  | TryCatch (l, ss, ccs) ->
    let state = List.fold_left f state ss in
    List.fold_left (fun state (_, _, _, ss) -> List.fold_left f state ss) state ccs
  | TryFinally (l, ssb, _, ssf) ->
    let state = List.fold_left f state ssb in
    List.fold_left f state ssf
  | BlockStmt (l, ds, ss, _, _) ->
    let process_decl state = function
      Func (_, _, _, _, _, _, _, (_, prototypeImplementationProof), _, _, body, _, _) ->
      let state = match body with None -> state | Some (ss, _) -> List.fold_left f state ss in
      begin match prototypeImplementationProof with
        None -> state
      | Some (_, ss) -> List.fold_left f state ss
      end
    | _ -> state
    in
    let state = List.fold_left process_decl state ds in
    List.fold_left f state ss
  | PerformActionStmt (l, _, _, _, _, _, _, _, ss, _, _, _) -> List.fold_left f state ss
  | ProduceLemmaFunctionPointerChunkStmt (l, _, proofo, ssbo) ->
    let state =
      match proofo with
        None -> state
      | Some (_, _, _, _, _, ss, _) -> List.fold_left f state ss
    in
    begin match ssbo with
      None -> state
    | Some ss -> f state ss
    end
  | ProduceFunctionPointerChunkStmt (l, ftn, fpe, targs, args, params, openBraceLoc, ss, closeBraceLoc) -> List.fold_left f state ss
  | _ -> state

let is_lvalue_ref_type_expr = function 
  | LValueRefTypeExpr _ -> true | _ -> false

(* Postfix fold *)
let stmt_fold f state s =
  let rec iter state s =
    let state = stmt_fold_open iter state s in
    f state s
  in
  iter state s

(* Postfix iter *)
let stmt_iter f s = stmt_fold (fun _ s -> f s) () s

let expr_fold_open iter state e =
  let rec iters state es =
    match es with
      [] -> state
    | e::es -> iters (iter state e) es
  and iterpat state pat =
    match pat with
      LitPat e -> iter state e
    | _ -> state
  and iterpatopt state patopt =
    match patopt with
      None -> state
    | Some pat -> iterpat state pat
  and iterpats state pats =
    match pats with
      [] -> state
    | pat::pats -> iterpats (iterpat state pat) pats
  and itercs state cs =
    match cs with
      [] -> state
    | SwitchExprClause (l, cn, pats, e)::cs -> itercs (iter state e) cs
  in
  match e with
    True l -> state
  | False l -> state
  | Null l -> state
  | Var (l, x) | WVar (l, x, _) -> state
  | TruncatingExpr (l, e) -> iter state e
  | Operation (l, op, es) -> iters state es
  | WOperation (l, op, es, t) -> iters state es
  | SliceExpr (l, p1, p2) -> iterpatopt (iterpatopt state p1) p2
  | IntLit (l, n, _, _, _) -> state
  | WIntLit (l, n) -> state
  | RealLit(l, n, _) -> state
  | StringLit (l, s) -> state
  | ClassLit (l, cn) -> state
  | Read (l, e0, f)
  | ActivatingRead (l, e0, f)
  | Select (l, e0, f) -> iter state e0
  | ArrayLengthExpr (l, e0) -> iter state e0
  | WRead (l, e0, fparent, tparams, fname, frange, targs, fstatic, fvalue, fghost) -> if fstatic then state else iter state e0
  | WReadUnionMember (l, e0, parent, name, index, range, isActivating) -> iter state e0
  | WSelect (l, e0, fparent, tparams, fname, frange, targs) -> iter state e0
  | WReadInductiveField (l, e0, ind_name, constr_name, field_name, targs, tp0, tp) -> iter state e0
  | ReadArray (l, a, i) -> let state = iter state a in let state = iter state i in state
  | WReadArray (l, a, tp, i) -> let state = iter state a in let state = iter state i in state
  | Deref (l, e0) -> iter state e0
  | WDeref (l, e0, tp) -> iter state e0
  | CallExpr (l, g, targes, pats0, pats, mb) -> let state = iterpats state pats0 in let state = iterpats state pats in state
  | ExprCallExpr (l, e, es) -> iterpats (iter state e) es
  | WPureFunCall (l, g, targs, args) -> iters state args
  | WPureFunValueCall (l, e, args) -> iters state (e::args)
  | WFunCall (l, g, targs, args, _) -> iters state args
  | WFunPtrCall (l, e, ftn, args) -> let state = iter state e in iters state args
  | WMethodCall (l, cn, m, pts, args, mb, tparamEnv) -> iters state args
  | NewObject (l, cn, args, targs) -> iters state args
  | NewArray (l, te, e0) -> iter state e0
  | NewArrayWithInitializer (l, te, es) -> iters state es
  | IfExpr (l, e1, e2, e3) -> iters state [e1; e2; e3]
  | SwitchExpr (l, e0, cs, cdef_opt) | WSwitchExpr (l, e0, _, _, cs, cdef_opt, _, _) -> let state = itercs (iter state e0) cs in (match cdef_opt with Some (l, e) -> iter state e | None -> state)
  | PredNameExpr (l, p) -> state
  | CastExpr (l, te, e0) -> iter state e0
  | Upcast (e, fromType, toType) -> iter state e
  | TypedExpr (e, t) -> iter state e
  | WidenedParameterArgument e -> iter state e
  | SizeofExpr (l, TypeExpr _) -> state
  | SizeofExpr (l, e) -> iter state e
  | AlignofExpr (l, te) -> state
  | TypeInfo (l, t) -> state
  | GenericExpr (l, e, cs, d) ->
    let state = iter state e in
    let rec iter_cases state = function
      [] -> state
    | (te, e)::cs ->
      let state = iter state e in
      iter_cases state cs
    in
    let state = iter_cases state cs in
    begin match d with
      None -> state
    | Some e -> iter state e
    end
  | AddressOf (l, e0) -> iter state e0
  | ProverTypeConversion (pt, pt0, e0) -> iter state e0
  | Unbox (e, t) -> iter state e
  | ArrayTypeExpr' (l, e) -> iter state e
  | AssignExpr (l, lhs, _, rhs) -> iter (iter state lhs) rhs
  | AssignOpExpr (l, lhs, op, rhs, post) -> iter (iter state lhs) rhs
  | WAssignOpExpr (l, lhs, x, rhs, post) -> iter (iter state lhs) rhs
  | CommaExpr (l, e1, e2) -> iter (iter state e1) e2
  | InstanceOfExpr(l, e, tp) -> iter state e
  | SuperMethodCall(_, _, args) -> iters state args
  | WSuperMethodCall(_, _, _, args, _) -> iters state args
  | InitializerList (l, es) -> iters state (List.map snd es)
  | CxxNew (_, _, Some e)
  | WCxxNew (_, _, Some e) -> iter state e
  | CxxNew (_, _, _)
  | WCxxNew (_, _, _) -> state
  | CxxDelete (_, arg) -> iter state arg
  | Typeid (_, e) -> iter state e
  | TypeExpr te -> state
  | PointsTo (l, e, kind, rhs) -> iterpat (iter state e) rhs
  | WPointsTo (l, e, tp, kind, rhs) -> iterpat (iter state e) rhs
  | PredAsn (l, g, targs, ies, es, _) -> iterpats (iterpats state ies) es
  | WPredAsn (l, g, _, targs, ies, es) -> iterpats (iterpats state ies) es
  | PredExprAsn (l, e, pats) -> iterpats (iter state e) pats
  | WPredExprAsn (l, e, pts, inputParamCount, pats) -> iterpats (iter state e) pats
  | InstPredAsn (l, e, g, index, pats) -> iterpats (iter (iter state e) index) pats
  | WInstPredAsn (l, e_opt, tns, cfin, tn, g, index, pats) ->
    let state = match e_opt with None -> state | Some e -> iter state e in
    iterpats (iter state index) pats
  | ExprAsn (l, e) -> iter state e
  | MatchAsn (l, e, pat) -> iterpat (iter state e) pat
  | WMatchAsn (l, e, pat, tp) -> iterpat (iter state e) pat
  | LetTypeAsn (l, x, t, p) -> state
  | TypePredExpr (l, t, x) -> state
  | WTypePredExpr (l, t, x) -> state
  | Sep (l, p1, p2) -> iter (iter state p1) p2
  | IfAsn (l, e, p1, p2) -> iter (iter (iter state e) p1) p2
  | WSwitchAsn (l, e, i, sacs) ->
    let rec iter' state = function
      [] -> state
    | WSwitchAsnClause (l, _, _, _, _, a)::sacs -> iter' (iter state e) sacs
    in
    iter' (iter state e) sacs
  | EmpAsn l -> state
  | ForallAsn (l, tp, i, e) -> iter state e
  | CoefAsn (l, coef, body) -> iter (iterpat state coef) body
  | EnsuresAsn (l, result_var, body) -> iter state body
  | _ -> static_error (expr_loc e) "This expression form is not allowed in this position." None

(* Postfix fold *)
let expr_fold f state e = let rec iter state e = f (expr_fold_open iter state e) e in iter state e

let expr_iter f e = expr_fold (fun state e -> f e) () e

let expr_flatmap f e = expr_fold (fun state e -> f e @ state) [] e

let rec make_addr_of (loc: loc) (expr: expr): expr =
  match expr with
  | CxxDerivedToBase (d_l, d_e, d_t) ->
    let addr_of_e = make_addr_of loc d_e in
    CxxDerivedToBase (d_l, addr_of_e, PtrTypeExpr (d_l, d_t))
  | _ ->
    AddressOf (loc, expr)
