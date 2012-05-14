type constant_value =
    IntConst of Big_int.big_int
  | BoolConst of bool
  | StringConst of string
  | NullConst
exception NotAConstant
type type_ =
    Bool
  | Void
  | IntType
  | UShortType
  | ShortType
  | UintPtrType
  | RealType
  | UChar
  | Char
  | StructType of string
  | PtrType of type_
  | FuncType of string
  | InductiveType of string * type_ list
  | PredType of string list * type_ list * int option
  | PureFuncType of type_ * type_
  | ObjType of string
  | ArrayType of type_
  | StaticArrayType of type_ * int
  | BoxIdType
  | HandleIdType
  | AnyType
  | TypeParam of string
  | InferredType of type_ option ref
  | ClassOrInterfaceName of string
  | PackageName of string
  | RefType of type_
  | PluginInternalType of DynType.dyn
type prover_type = ProverInt | ProverBool | ProverReal | ProverInductive
type type_expr =
    StructTypeExpr of Lexer.loc * string
  | PtrTypeExpr of Lexer.loc * type_expr
  | ArrayTypeExpr of Lexer.loc * type_expr
  | StaticArrayTypeExpr of Lexer.loc * type_expr * int
  | ManifestTypeExpr of Lexer.loc * type_
  | IdentTypeExpr of Lexer.loc * string option * string
  | ConstructedTypeExpr of Lexer.loc * string * type_expr list
  | PredTypeExpr of Lexer.loc * type_expr list * int option
  | PureFuncTypeExpr of Lexer.loc * type_expr list
class predref :
  string ->
  object
    val mutable domain : type_ list option
    val mutable inputParamCount : int option option
    val mutable tparamcount : int option
    method domain : type_ list
    method inputParamCount : int option
    method name : string
    method set_domain : type_ list -> unit
    method set_inputParamCount : int option -> unit
  end
type ident_scope =
    LocalVar
  | PureCtor
  | FuncName
  | PredFamName
  | EnumElemName of Big_int.big_int
  | GlobalName
  | ModuleName
  | PureFuncName
type operator =
    Add
  | Sub
  | Le
  | Lt
  | Eq
  | Neq
  | And
  | Or
  | Xor
  | Not
  | Mul
  | Div
  | Mod
  | BitNot
  | BitAnd
  | BitXor
  | BitOr
  | ShiftLeft
  | ShiftRight
and expr =
    True of Lexer.loc
  | False of Lexer.loc
  | Null of Lexer.loc
  | Var of Lexer.loc * string * ident_scope option ref
  | Operation of Lexer.loc * operator * expr list * type_ list option ref
  | IntLit of Lexer.loc * Big_int.big_int * type_ option ref
  | RealLit of Lexer.loc * Num.num
  | StringLit of Lexer.loc * string
  | ClassLit of Lexer.loc * string
  | Read of Lexer.loc * expr * string
  | ArrayLengthExpr of Lexer.loc * expr
  | WRead of Lexer.loc * expr * string * string * type_ * bool *
      constant_value option option ref * ghostness
  | ReadArray of Lexer.loc * expr * expr
  | WReadArray of Lexer.loc * expr * type_ * expr
  | Deref of Lexer.loc * expr * type_ option ref
  | CallExpr of Lexer.loc * string * type_expr list * pat list * pat list *
      method_binding
  | ExprCallExpr of Lexer.loc * expr * expr list
  | WFunPtrCall of Lexer.loc * string * expr list
  | WPureFunCall of Lexer.loc * string * type_ list * expr list
  | WPureFunValueCall of Lexer.loc * expr * expr list
  | WFunCall of Lexer.loc * string * type_ list * expr list
  | WMethodCall of Lexer.loc * string * string * type_ list * expr list *
      method_binding
  | NewArray of Lexer.loc * type_expr * expr
  | NewObject of Lexer.loc * string * expr list
  | NewArrayWithInitializer of Lexer.loc * type_expr * expr list
  | IfExpr of Lexer.loc * expr * expr * expr
  | SwitchExpr of Lexer.loc * expr * switch_expr_clause list *
      (Lexer.loc * expr) option *
      (type_ * (string * type_) list * type_ list * type_) option ref
  | PredNameExpr of Lexer.loc * string
  | CastExpr of Lexer.loc * bool * type_expr * expr
  | Upcast of expr * type_ * type_
  | WidenedParameterArgument of expr
  | SizeofExpr of Lexer.loc * type_expr
  | AddressOf of Lexer.loc * expr
  | ProverTypeConversion of prover_type * prover_type * expr
  | ArrayTypeExpr' of Lexer.loc * expr
  | AssignExpr of Lexer.loc * expr * expr
  | AssignOpExpr of Lexer.loc * expr * operator * expr * bool *
      type_ list option ref * type_ option ref
  | InstanceOfExpr of Lexer.loc * expr * type_expr
  | SuperMethodCall of Lexer.loc * string * expr list
  | WSuperMethodCall of Lexer.loc * string * expr list *
      (Lexer.loc * ghostness * type_ option * (string * type_) list * 
       asn * asn * (type_ * asn) list * visibility)
  | InitializerList of Lexer.loc * expr list
and pat =
    LitPat of expr
  | VarPat of Lexer.loc * string
  | DummyPat
  | CtorPat of Lexer.loc * string * pat list
  | WCtorPat of Lexer.loc * string * type_ list * string * type_ list *
      type_ list * pat list
and switch_expr_clause =
    SwitchExprClause of Lexer.loc * string * string list * expr
and language = Java | CLang
and method_binding = Static | Instance
and visibility = Public | Protected | Private | Package
and package = PackageDecl of Lexer.loc * string * import list * decl list
and import = Import of Lexer.loc * string * string option
and stmt =
    PureStmt of Lexer.loc * stmt
  | NonpureStmt of Lexer.loc * bool * stmt
  | DeclStmt of Lexer.loc *
      (Lexer.loc * type_expr * string * expr option * bool ref) list
  | ExprStmt of expr
  | IfStmt of Lexer.loc * expr * stmt list * stmt list
  | SwitchStmt of Lexer.loc * expr * switch_stmt_clause list
  | Assert of Lexer.loc * asn
  | Leak of Lexer.loc * asn
  | Open of Lexer.loc * expr option * string * type_expr list * pat list *
      pat list * pat option
  | Close of Lexer.loc * expr option * string * type_expr list * pat list *
      pat list * pat option
  | ReturnStmt of Lexer.loc * expr option
  | WhileStmt of Lexer.loc * expr * loop_spec option * expr option *
      stmt list
  | BlockStmt of Lexer.loc * decl list * stmt list * Lexer.loc *
      string list ref
  | PerformActionStmt of Lexer.loc * bool ref * string * pat list *
      Lexer.loc * string * pat list * Lexer.loc * string * expr list *
      stmt list * Lexer.loc * (Lexer.loc * expr list) option * Lexer.loc *
      string * expr list
  | SplitFractionStmt of Lexer.loc * string * type_expr list * pat list *
      expr option
  | MergeFractionsStmt of Lexer.loc * string * type_expr list * pat list
  | CreateBoxStmt of Lexer.loc * string * string * expr list *
      (Lexer.loc * string * string * expr list) list
  | CreateHandleStmt of Lexer.loc * string * string * expr
  | DisposeBoxStmt of Lexer.loc * string * pat list *
      (Lexer.loc * string * pat list) list
  | LabelStmt of Lexer.loc * string
  | GotoStmt of Lexer.loc * string
  | NoopStmt of Lexer.loc
  | InvariantStmt of Lexer.loc * asn
  | ProduceLemmaFunctionPointerChunkStmt of Lexer.loc * expr *
      (string * type_expr list * expr list * (Lexer.loc * string) list *
       Lexer.loc * stmt list * Lexer.loc)
      option * stmt option
  | ProduceFunctionPointerChunkStmt of Lexer.loc * string * expr *
      expr list * (Lexer.loc * string) list * Lexer.loc * stmt list *
      Lexer.loc
  | Throw of Lexer.loc * expr
  | TryCatch of Lexer.loc * stmt list *
      (Lexer.loc * type_expr * string * stmt list) list
  | TryFinally of Lexer.loc * stmt list * Lexer.loc * stmt list
  | Break of Lexer.loc
  | SuperConstructorCall of Lexer.loc * expr list
and loop_spec = LoopInv of asn | LoopSpec of asn * asn
and switch_stmt_clause =
    SwitchStmtClause of Lexer.loc * expr * stmt list
  | SwitchStmtDefaultClause of Lexer.loc * stmt list
and asn =
    PointsTo of Lexer.loc * expr * pat
  | WPointsTo of Lexer.loc * expr * type_ * pat
  | PredAsn of Lexer.loc * predref * type_expr list * pat list * pat list
  | WPredAsn of Lexer.loc * predref * bool * type_ list * pat list * pat list
  | InstPredAsn of Lexer.loc * expr * string * expr * pat list
  | WInstPredAsn of Lexer.loc * expr option * string * class_finality *
      string * string * expr * pat list
  | ExprAsn of Lexer.loc * expr
  | Sep of Lexer.loc * asn * asn
  | IfAsn of Lexer.loc * expr * asn * asn
  | SwitchAsn of Lexer.loc * expr * switch_asn_clause list
  | WSwitchAsn of Lexer.loc * expr * string * switch_asn_clause list
  | EmpAsn of Lexer.loc
  | ForallAsn of Lexer.loc * string * expr
  | CoefAsn of Lexer.loc * pat * asn
  | PluginAsn of Lexer.loc * string
  | WPluginAsn of Lexer.loc * string list *
      Plugins.typechecked_plugin_assertion
and switch_asn_clause =
    SwitchAsnClause of Lexer.loc * string * string list *
      prover_type option list option ref * asn
and func_kind = Regular | Fixpoint | Lemma of bool * expr option
and meth =
    Meth of Lexer.loc * ghostness * type_expr option * string *
      (type_expr * string) list *
      (asn * asn * (type_expr * asn) list) option *
      (stmt list * Lexer.loc) option * method_binding * visibility * 
      bool
and cons =
    Cons of Lexer.loc * (type_expr * string) list *
      (asn * asn * (type_expr * asn) list) option *
      (stmt list * Lexer.loc) option * visibility
and instance_pred_decl =
    InstancePredDecl of Lexer.loc * string * (type_expr * string) list *
      asn option
and class_finality = FinalClass | ExtensibleClass
and decl =
    Struct of Lexer.loc * string * field list option
  | Inductive of Lexer.loc * string * string list * ctor list
  | Class of Lexer.loc * bool * class_finality * string * meth list *
      field list * cons list * string * string list * instance_pred_decl list
  | Interface of Lexer.loc * string * string list * field list * meth list *
      instance_pred_decl list
  | PredFamilyDecl of Lexer.loc * string * string list * int *
      type_expr list * int option
  | PredFamilyInstanceDecl of Lexer.loc * string * string list *
      (Lexer.loc * string) list * (type_expr * string) list * asn
  | PredCtorDecl of Lexer.loc * string * (type_expr * string) list *
      (type_expr * string) list * asn
  | Func of Lexer.loc * func_kind * string list * type_expr option * 
      string * (type_expr * string) list * bool *
      (string * type_expr list * (Lexer.loc * string) list) option *
      (asn * asn) option * (stmt list * Lexer.loc) option * method_binding *
      visibility
  | TypedefDecl of Lexer.loc * type_expr * string
  | FuncTypeDecl of Lexer.loc * ghostness * type_expr option * string *
      string list * (type_expr * string) list * (type_expr * string) list *
      (asn * asn)
  | BoxClassDecl of Lexer.loc * string * (type_expr * string) list * 
      asn * action_decl list * handle_pred_decl list
  | EnumDecl of Lexer.loc * string * (string * expr option) list
  | Global of Lexer.loc * type_expr * string * expr option
  | UnloadableModuleDecl of Lexer.loc
  | LoadPluginDecl of Lexer.loc * Lexer.loc * string
and action_decl =
    ActionDecl of Lexer.loc * string * (type_expr * string) list * expr *
      expr
and handle_pred_decl =
    HandlePredDecl of Lexer.loc * string * (type_expr * string) list * 
      expr * preserved_by_clause list
and preserved_by_clause =
    PreservedByClause of Lexer.loc * string * string list * stmt list
and ghostness = Ghost | Real
and field =
    Field of Lexer.loc * ghostness * type_expr * string * method_binding *
      visibility * bool * expr option
and ctor = Ctor of Lexer.loc * string * type_expr list
and member =
    FieldMember of field list
  | MethMember of meth
  | ConsMember of cons
  | PredMember of instance_pred_decl
val func_kind_of_ghostness : ghostness -> func_kind
val string_of_srcpos : string * int * int -> string
val string_of_path : string * string -> string
val string_of_loc :
  ((string * string) * int * int) * ((string * string) * int * int) -> string
val string_of_func_kind : func_kind -> string
val tostring : method_binding -> string
val expr_loc : expr -> Lexer.loc
val asn_loc : asn -> Lexer.loc
val stmt_loc : stmt -> Lexer.loc
val type_expr_loc : type_expr -> Lexer.loc
val expr_fold_open : ('a -> expr -> 'a) -> 'a -> expr -> 'a
val expr_fold : ('a -> expr -> 'a) -> 'a -> expr -> 'a
val expr_iter : (expr -> unit) -> expr -> unit
val expr_flatmap : (expr -> 'a list) -> expr -> 'a list
