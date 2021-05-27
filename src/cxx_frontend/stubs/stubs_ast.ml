[@@@ocaml.warning "-27-32-37-60"]

type ro = Capnp.Message.ro
type rw = Capnp.Message.rw

module type S = sig
  module MessageWrapper : Capnp.RPC.S
  type 'cap message_t = 'cap MessageWrapper.Message.t
  type 'a reader_t = 'a MessageWrapper.StructStorage.reader_t
  type 'a builder_t = 'a MessageWrapper.StructStorage.builder_t

  module NbBase_15750048951651279863 : sig
    type t =
      | Decimal
      | Octal
      | Hex
      | Undefined of int
  end
  module SufKind_10349718269051794478 : sig
    type t =
      | LSuf
      | LLSuf
      | NoSuf
      | Undefined of int
  end
  module BinaryOpKind_15775553773985184773 : sig
    type t =
      | Add
      | Sub
      | Assign
      | Mul
      | Div
      | Rem
      | Shl
      | Shr
      | Lt
      | Gt
      | Le
      | Ge
      | Eq
      | Ne
      | And
      | Or
      | Xor
      | LAnd
      | LOr
      | MulAssign
      | DivAssign
      | RemAssign
      | AddAssign
      | SubAssign
      | ShlAssign
      | ShrAssign
      | AndAssign
      | XorAssign
      | OrAssign
      | Undefined of int
  end
  module UnaryOpKind_16270584510146119878 : sig
    type t =
      | Plus
      | Minus
      | Not
      | LNot
      | AddrOf
      | Deref
      | PreInc
      | PreDec
      | PostInc
      | PostDec
      | Undefined of int
  end
  module InitStyle_13739150215916644662 : sig
    type t =
      | CopyInit
      | ListInit
      | Undefined of int
  end
  module InitStyle_15285372864656172726 : sig
    type t =
      | CInit
      | CallInit
      | ListInit
      | Undefined of int
  end
  module RecordKind_12907431634679073908 : sig
    type t =
      | Struc
      | Class
      | Unio
      | Undefined of int
  end
  module BuiltinKind_11913544707969661485 : sig
    type t =
      | Char
      | UChar
      | Short
      | UShort
      | Void
      | Bool
      | Int
      | UInt
      | Long
      | ULong
      | LongLong
      | ULongLong
      | Undefined of int
  end

  module Reader : sig
    type array_t
    type builder_array_t
    type pointer_t = ro MessageWrapper.Slice.t option
    val of_pointer : pointer_t -> 'a reader_t
    module Loc : sig
      type struct_t = [`Loc_b1436df23fb200b4]
      type t = struct_t reader_t
      module SrcPos : sig
        type struct_t = [`SrcPos_80bc3ef5a3c049a0]
        type t = struct_t reader_t
        val l_get : t -> int
        val c_get : t -> int
        val fd_get : t -> int
        val of_message : 'cap message_t -> t
        val of_builder : struct_t builder_t -> t
      end
      val has_start : t -> bool
      val start_get : t -> [`SrcPos_80bc3ef5a3c049a0] reader_t
      val start_get_pipelined : struct_t MessageWrapper.StructRef.t -> [`SrcPos_80bc3ef5a3c049a0] MessageWrapper.StructRef.t
      val has_end : t -> bool
      val end_get : t -> [`SrcPos_80bc3ef5a3c049a0] reader_t
      val end_get_pipelined : struct_t MessageWrapper.StructRef.t -> [`SrcPos_80bc3ef5a3c049a0] MessageWrapper.StructRef.t
      val of_message : 'cap message_t -> t
      val of_builder : struct_t builder_t -> t
    end
    module Node : sig
      type struct_t = [`Node_e2a8b78aa50d684a]
      type t = struct_t reader_t
      val has_loc : t -> bool
      val loc_get : t -> Loc.t
      val loc_get_pipelined : struct_t MessageWrapper.StructRef.t -> Loc.struct_t MessageWrapper.StructRef.t
      val desc_get : t -> pointer_t
      val desc_get_interface : t -> 'a MessageWrapper.Capability.t option
      val of_message : 'cap message_t -> t
      val of_builder : struct_t builder_t -> t
    end
    module Type : sig
      type struct_t = [`Type_f4d8929c89991d82]
      type t = struct_t reader_t
      module BuiltinKind : sig
        type t = BuiltinKind_11913544707969661485.t =
          | Char
          | UChar
          | Short
          | UShort
          | Void
          | Bool
          | Int
          | UInt
          | Long
          | ULong
          | LongLong
          | ULongLong
          | Undefined of int
      end
      module Record : sig
        type struct_t = [`Record_f92013bb699d0281]
        type t = struct_t reader_t
        val kind_get : t -> RecordKind_12907431634679073908.t
        val has_name : t -> bool
        val name_get : t -> string
        val of_message : 'cap message_t -> t
        val of_builder : struct_t builder_t -> t
      end
      type unnamed_union_t =
        | Builtin of BuiltinKind_11913544707969661485.t
        | Pointer of [`Type_f4d8929c89991d82] reader_t
        | PointerLoc of Node.t
        | Record of [`Record_f92013bb699d0281] reader_t
        | EnumType of string
        | Undefined of int
      val get : t -> unnamed_union_t
      val of_message : 'cap message_t -> t
      val of_builder : struct_t builder_t -> t
    end
    module Stmt : sig
      type struct_t = [`Stmt_f6a0f771ad50816c]
      type t = struct_t reader_t
      module Return : sig
        type struct_t = [`Return_fe7af58e3af28b84]
        type t = struct_t reader_t
        val has_expr : t -> bool
        val expr_get : t -> Node.t
        val expr_get_pipelined : struct_t MessageWrapper.StructRef.t -> Node.struct_t MessageWrapper.StructRef.t
        val of_message : 'cap message_t -> t
        val of_builder : struct_t builder_t -> t
      end
      module If : sig
        type struct_t = [`If_bfef959001088175]
        type t = struct_t reader_t
        val has_cond : t -> bool
        val cond_get : t -> Node.t
        val cond_get_pipelined : struct_t MessageWrapper.StructRef.t -> Node.struct_t MessageWrapper.StructRef.t
        val has_then : t -> bool
        val then_get : t -> Node.t
        val then_get_pipelined : struct_t MessageWrapper.StructRef.t -> Node.struct_t MessageWrapper.StructRef.t
        val has_else : t -> bool
        val else_get : t -> Node.t
        val else_get_pipelined : struct_t MessageWrapper.StructRef.t -> Node.struct_t MessageWrapper.StructRef.t
        val of_message : 'cap message_t -> t
        val of_builder : struct_t builder_t -> t
      end
      module Compound : sig
        type struct_t = [`Compound_899b868295a7b9ce]
        type t = struct_t reader_t
        val has_stmts : t -> bool
        val stmts_get : t -> (ro, Node.t, array_t) Capnp.Array.t
        val stmts_get_list : t -> Node.t list
        val stmts_get_array : t -> Node.t array
        val has_r_brace : t -> bool
        val r_brace_get : t -> Loc.t
        val r_brace_get_pipelined : struct_t MessageWrapper.StructRef.t -> Loc.struct_t MessageWrapper.StructRef.t
        val of_message : 'cap message_t -> t
        val of_builder : struct_t builder_t -> t
      end
      module While : sig
        type struct_t = [`While_ef7716d0539edb37]
        type t = struct_t reader_t
        val has_cond : t -> bool
        val cond_get : t -> Node.t
        val cond_get_pipelined : struct_t MessageWrapper.StructRef.t -> Node.struct_t MessageWrapper.StructRef.t
        val has_body : t -> bool
        val body_get : t -> Node.t
        val body_get_pipelined : struct_t MessageWrapper.StructRef.t -> Node.struct_t MessageWrapper.StructRef.t
        val has_spec : t -> bool
        val spec_get : t -> (ro, [`Clause_adb9aafdab430c1d] reader_t, array_t) Capnp.Array.t
        val spec_get_list : t -> [`Clause_adb9aafdab430c1d] reader_t list
        val spec_get_array : t -> [`Clause_adb9aafdab430c1d] reader_t array
        val has_while_loc : t -> bool
        val while_loc_get : t -> Loc.t
        val while_loc_get_pipelined : struct_t MessageWrapper.StructRef.t -> Loc.struct_t MessageWrapper.StructRef.t
        val of_message : 'cap message_t -> t
        val of_builder : struct_t builder_t -> t
      end
      module Case : sig
        type struct_t = [`Case_d41d9dffe36da558]
        type t = struct_t reader_t
        val has_lhs : t -> bool
        val lhs_get : t -> Node.t
        val lhs_get_pipelined : struct_t MessageWrapper.StructRef.t -> Node.struct_t MessageWrapper.StructRef.t
        val has_stmt : t -> bool
        val stmt_get : t -> Node.t
        val stmt_get_pipelined : struct_t MessageWrapper.StructRef.t -> Node.struct_t MessageWrapper.StructRef.t
        val of_message : 'cap message_t -> t
        val of_builder : struct_t builder_t -> t
      end
      module DefCase : sig
        type struct_t = [`DefCase_ef0bcc479ff59f3e]
        type t = struct_t reader_t
        val has_stmt : t -> bool
        val stmt_get : t -> Node.t
        val stmt_get_pipelined : struct_t MessageWrapper.StructRef.t -> Node.struct_t MessageWrapper.StructRef.t
        val of_message : 'cap message_t -> t
        val of_builder : struct_t builder_t -> t
      end
      module Switch : sig
        type struct_t = [`Switch_ffc6828955aafac4]
        type t = struct_t reader_t
        val has_cond : t -> bool
        val cond_get : t -> Node.t
        val cond_get_pipelined : struct_t MessageWrapper.StructRef.t -> Node.struct_t MessageWrapper.StructRef.t
        val has_cases : t -> bool
        val cases_get : t -> (ro, Node.t, array_t) Capnp.Array.t
        val cases_get_list : t -> Node.t list
        val cases_get_array : t -> Node.t array
        val of_message : 'cap message_t -> t
        val of_builder : struct_t builder_t -> t
      end
      type unnamed_union_t =
        | UnionNotInitialized
        | Ann of string
        | Decl of (ro, Node.t, array_t) Capnp.Array.t
        | Compound of [`Compound_899b868295a7b9ce] reader_t
        | Expr of Node.t
        | Return of [`Return_fe7af58e3af28b84] reader_t
        | If of [`If_bfef959001088175] reader_t
        | Null
        | While of [`While_ef7716d0539edb37] reader_t
        | DoWhile of [`While_ef7716d0539edb37] reader_t
        | Break
        | Continue
        | Switch of [`Switch_ffc6828955aafac4] reader_t
        | Case of [`Case_d41d9dffe36da558] reader_t
        | DefCase of [`DefCase_ef0bcc479ff59f3e] reader_t
        | Undefined of int
      val get : t -> unnamed_union_t
      val of_message : 'cap message_t -> t
      val of_builder : struct_t builder_t -> t
    end
    module Clause : sig
      type struct_t = [`Clause_adb9aafdab430c1d]
      type t = struct_t reader_t
      val has_loc : t -> bool
      val loc_get : t -> Loc.t
      val loc_get_pipelined : struct_t MessageWrapper.StructRef.t -> Loc.struct_t MessageWrapper.StructRef.t
      val has_text : t -> bool
      val text_get : t -> string
      val of_message : 'cap message_t -> t
      val of_builder : struct_t builder_t -> t
    end
    module RecordKind : sig
      type t = RecordKind_12907431634679073908.t =
        | Struc
        | Class
        | Unio
        | Undefined of int
    end
    module Decl : sig
      type struct_t = [`Decl_d96c7f8624e22938]
      type t = struct_t reader_t
      module Param : sig
        type struct_t = [`Param_97bce41c55c2994a]
        type t = struct_t reader_t
        val has_type : t -> bool
        val type_get : t -> Node.t
        val type_get_pipelined : struct_t MessageWrapper.StructRef.t -> Node.struct_t MessageWrapper.StructRef.t
        val has_name : t -> bool
        val name_get : t -> string
        val has_default : t -> bool
        val default_get : t -> Node.t
        val default_get_pipelined : struct_t MessageWrapper.StructRef.t -> Node.struct_t MessageWrapper.StructRef.t
        val of_message : 'cap message_t -> t
        val of_builder : struct_t builder_t -> t
      end
      module Var : sig
        type struct_t = [`Var_8da2907bb130c41c]
        type t = struct_t reader_t
        module InitStyle : sig
          type t = InitStyle_15285372864656172726.t =
            | CInit
            | CallInit
            | ListInit
            | Undefined of int
        end
        module VarInit : sig
          type struct_t = [`VarInit_96ff0430cb165092]
          type t = struct_t reader_t
          val has_init : t -> bool
          val init_get : t -> Node.t
          val init_get_pipelined : struct_t MessageWrapper.StructRef.t -> Node.struct_t MessageWrapper.StructRef.t
          val style_get : t -> InitStyle.t
          val of_message : 'cap message_t -> t
          val of_builder : struct_t builder_t -> t
        end
        val has_name : t -> bool
        val name_get : t -> string
        val has_type : t -> bool
        val type_get : t -> Node.t
        val type_get_pipelined : struct_t MessageWrapper.StructRef.t -> Node.struct_t MessageWrapper.StructRef.t
        val has_init : t -> bool
        val init_get : t -> [`VarInit_96ff0430cb165092] reader_t
        val init_get_pipelined : struct_t MessageWrapper.StructRef.t -> [`VarInit_96ff0430cb165092] MessageWrapper.StructRef.t
        val of_message : 'cap message_t -> t
        val of_builder : struct_t builder_t -> t
      end
      module Function : sig
        type struct_t = [`Function_d64c65470b140c81]
        type t = struct_t reader_t
        val has_name : t -> bool
        val name_get : t -> string
        val has_body : t -> bool
        val body_get : t -> Node.t
        val body_get_pipelined : struct_t MessageWrapper.StructRef.t -> Node.struct_t MessageWrapper.StructRef.t
        val has_result : t -> bool
        val result_get : t -> Node.t
        val result_get_pipelined : struct_t MessageWrapper.StructRef.t -> Node.struct_t MessageWrapper.StructRef.t
        val has_params : t -> bool
        val params_get : t -> (ro, Param.t, array_t) Capnp.Array.t
        val params_get_list : t -> Param.t list
        val params_get_array : t -> Param.t array
        val has_contract : t -> bool
        val contract_get : t -> (ro, Clause.t, array_t) Capnp.Array.t
        val contract_get_list : t -> Clause.t list
        val contract_get_array : t -> Clause.t array
        val of_message : 'cap message_t -> t
        val of_builder : struct_t builder_t -> t
      end
      module Field : sig
        type struct_t = [`Field_ca43d1968400194b]
        type t = struct_t reader_t
        module InitStyle : sig
          type t = InitStyle_13739150215916644662.t =
            | CopyInit
            | ListInit
            | Undefined of int
        end
        module FieldInit : sig
          type struct_t = [`FieldInit_91afac6d2dc82432]
          type t = struct_t reader_t
          val has_init : t -> bool
          val init_get : t -> Node.t
          val init_get_pipelined : struct_t MessageWrapper.StructRef.t -> Node.struct_t MessageWrapper.StructRef.t
          val style_get : t -> InitStyle.t
          val of_message : 'cap message_t -> t
          val of_builder : struct_t builder_t -> t
        end
        val has_name : t -> bool
        val name_get : t -> string
        val has_type : t -> bool
        val type_get : t -> Node.t
        val type_get_pipelined : struct_t MessageWrapper.StructRef.t -> Node.struct_t MessageWrapper.StructRef.t
        val has_init : t -> bool
        val init_get : t -> [`FieldInit_91afac6d2dc82432] reader_t
        val init_get_pipelined : struct_t MessageWrapper.StructRef.t -> [`FieldInit_91afac6d2dc82432] MessageWrapper.StructRef.t
        val of_message : 'cap message_t -> t
        val of_builder : struct_t builder_t -> t
      end
      module Record : sig
        type struct_t = [`Record_c925b09644ce72d3]
        type t = struct_t reader_t
        val has_name : t -> bool
        val name_get : t -> string
        val kind_get : t -> RecordKind.t
        val has_fields : t -> bool
        val fields_get : t -> (ro, Node.t, array_t) Capnp.Array.t
        val fields_get_list : t -> Node.t list
        val fields_get_array : t -> Node.t array
        val has_methods : t -> bool
        val methods_get : t -> (ro, Node.t, array_t) Capnp.Array.t
        val methods_get_list : t -> Node.t list
        val methods_get_array : t -> Node.t array
        val has_def_get : t -> bool
        val has_decls : t -> bool
        val decls_get : t -> (ro, Node.t, array_t) Capnp.Array.t
        val decls_get_list : t -> Node.t list
        val decls_get_array : t -> Node.t array
        val of_message : 'cap message_t -> t
        val of_builder : struct_t builder_t -> t
      end
      module Method : sig
        type struct_t = [`Method_bebeef9161eb7d3c]
        type t = struct_t reader_t
        val static_get : t -> bool
        val has_func : t -> bool
        val func_get : t -> Function.t
        val func_get_pipelined : struct_t MessageWrapper.StructRef.t -> Function.struct_t MessageWrapper.StructRef.t
        val has_this : t -> bool
        val this_get : t -> Type.t
        val this_get_pipelined : struct_t MessageWrapper.StructRef.t -> Type.struct_t MessageWrapper.StructRef.t
        val of_message : 'cap message_t -> t
        val of_builder : struct_t builder_t -> t
      end
      module Typedef : sig
        type struct_t = [`Typedef_e46ae190d3365bca]
        type t = struct_t reader_t
        val has_type : t -> bool
        val type_get : t -> Node.t
        val type_get_pipelined : struct_t MessageWrapper.StructRef.t -> Node.struct_t MessageWrapper.StructRef.t
        val has_name : t -> bool
        val name_get : t -> string
        val of_message : 'cap message_t -> t
        val of_builder : struct_t builder_t -> t
      end
      module Enum : sig
        type struct_t = [`Enum_daecdb4dcd868ea8]
        type t = struct_t reader_t
        module EnumField : sig
          type struct_t = [`EnumField_87676bdbadd4545d]
          type t = struct_t reader_t
          val has_name : t -> bool
          val name_get : t -> string
          val has_expr : t -> bool
          val expr_get : t -> Node.t
          val expr_get_pipelined : struct_t MessageWrapper.StructRef.t -> Node.struct_t MessageWrapper.StructRef.t
          val of_message : 'cap message_t -> t
          val of_builder : struct_t builder_t -> t
        end
        val has_name : t -> bool
        val name_get : t -> string
        val has_fields : t -> bool
        val fields_get : t -> (ro, [`EnumField_87676bdbadd4545d] reader_t, array_t) Capnp.Array.t
        val fields_get_list : t -> [`EnumField_87676bdbadd4545d] reader_t list
        val fields_get_array : t -> [`EnumField_87676bdbadd4545d] reader_t array
        val of_message : 'cap message_t -> t
        val of_builder : struct_t builder_t -> t
      end
      type unnamed_union_t =
        | UnionNotInitialized
        | Ann of string
        | Empty
        | Var of [`Var_8da2907bb130c41c] reader_t
        | Function of [`Function_d64c65470b140c81] reader_t
        | Field of [`Field_ca43d1968400194b] reader_t
        | Record of [`Record_c925b09644ce72d3] reader_t
        | Method of [`Method_bebeef9161eb7d3c] reader_t
        | AccessSpec
        | DefDestructor
        | DefConstructor
        | Typedef of [`Typedef_e46ae190d3365bca] reader_t
        | EnumDecl of [`Enum_daecdb4dcd868ea8] reader_t
        | Undefined of int
      val get : t -> unnamed_union_t
      val of_message : 'cap message_t -> t
      val of_builder : struct_t builder_t -> t
    end
    module UnaryOpKind : sig
      type t = UnaryOpKind_16270584510146119878.t =
        | Plus
        | Minus
        | Not
        | LNot
        | AddrOf
        | Deref
        | PreInc
        | PreDec
        | PostInc
        | PostDec
        | Undefined of int
    end
    module BinaryOpKind : sig
      type t = BinaryOpKind_15775553773985184773.t =
        | Add
        | Sub
        | Assign
        | Mul
        | Div
        | Rem
        | Shl
        | Shr
        | Lt
        | Gt
        | Le
        | Ge
        | Eq
        | Ne
        | And
        | Or
        | Xor
        | LAnd
        | LOr
        | MulAssign
        | DivAssign
        | RemAssign
        | AddAssign
        | SubAssign
        | ShlAssign
        | ShrAssign
        | AndAssign
        | XorAssign
        | OrAssign
        | Undefined of int
    end
    module SufKind : sig
      type t = SufKind_10349718269051794478.t =
        | LSuf
        | LLSuf
        | NoSuf
        | Undefined of int
    end
    module NbBase : sig
      type t = NbBase_15750048951651279863.t =
        | Decimal
        | Octal
        | Hex
        | Undefined of int
    end
    module Expr : sig
      type struct_t = [`Expr_d5d009cc85c86562]
      type t = struct_t reader_t
      module UnaryOp : sig
        type struct_t = [`UnaryOp_b525d86a8f48e679]
        type t = struct_t reader_t
        val has_operand : t -> bool
        val operand_get : t -> Node.t
        val operand_get_pipelined : struct_t MessageWrapper.StructRef.t -> Node.struct_t MessageWrapper.StructRef.t
        val kind_get : t -> UnaryOpKind.t
        val of_message : 'cap message_t -> t
        val of_builder : struct_t builder_t -> t
      end
      module BinaryOp : sig
        type struct_t = [`BinaryOp_b95e9a5df08d277c]
        type t = struct_t reader_t
        val has_lhs : t -> bool
        val lhs_get : t -> Node.t
        val lhs_get_pipelined : struct_t MessageWrapper.StructRef.t -> Node.struct_t MessageWrapper.StructRef.t
        val has_rhs : t -> bool
        val rhs_get : t -> Node.t
        val rhs_get_pipelined : struct_t MessageWrapper.StructRef.t -> Node.struct_t MessageWrapper.StructRef.t
        val kind_get : t -> BinaryOpKind.t
        val of_message : 'cap message_t -> t
        val of_builder : struct_t builder_t -> t
      end
      module IntLit : sig
        type struct_t = [`IntLit_a21731ff472a9631]
        type t = struct_t reader_t
        val has_value : t -> bool
        val value_get : t -> string
        val u_suffix_get : t -> bool
        val l_suffix_get : t -> SufKind.t
        val base_get : t -> NbBase.t
        val of_message : 'cap message_t -> t
        val of_builder : struct_t builder_t -> t
      end
      module Call : sig
        type struct_t = [`Call_d6c567dfeede9b58]
        type t = struct_t reader_t
        val has_args : t -> bool
        val args_get : t -> (ro, Node.t, array_t) Capnp.Array.t
        val args_get_list : t -> Node.t list
        val args_get_array : t -> Node.t array
        val has_callee : t -> bool
        val callee_get : t -> Node.t
        val callee_get_pipelined : struct_t MessageWrapper.StructRef.t -> Node.struct_t MessageWrapper.StructRef.t
        val of_message : 'cap message_t -> t
        val of_builder : struct_t builder_t -> t
      end
      module Member : sig
        type struct_t = [`Member_ab509764d68e7721]
        type t = struct_t reader_t
        val has_base : t -> bool
        val base_get : t -> Node.t
        val base_get_pipelined : struct_t MessageWrapper.StructRef.t -> Node.struct_t MessageWrapper.StructRef.t
        val has_name : t -> bool
        val name_get : t -> string
        val arrow_get : t -> bool
        val of_message : 'cap message_t -> t
        val of_builder : struct_t builder_t -> t
      end
      module New : sig
        type struct_t = [`New_e0dbc3751d359960]
        type t = struct_t reader_t
        val has_type : t -> bool
        val type_get : t -> Type.t
        val type_get_pipelined : struct_t MessageWrapper.StructRef.t -> Type.struct_t MessageWrapper.StructRef.t
        val has_expr : t -> bool
        val expr_get : t -> Node.t
        val expr_get_pipelined : struct_t MessageWrapper.StructRef.t -> Node.struct_t MessageWrapper.StructRef.t
        val of_message : 'cap message_t -> t
        val of_builder : struct_t builder_t -> t
      end
      type unnamed_union_t =
        | UnionNotInitialized
        | UnaryOp of [`UnaryOp_b525d86a8f48e679] reader_t
        | BinaryOp of [`BinaryOp_b95e9a5df08d277c] reader_t
        | BoolLit of bool
        | IntLit of [`IntLit_a21731ff472a9631] reader_t
        | StringLit of string
        | Call of [`Call_d6c567dfeede9b58] reader_t
        | DeclRef of string
        | Member of [`Member_ab509764d68e7721] reader_t
        | This
        | MemberCall of [`Call_d6c567dfeede9b58] reader_t
        | New of [`New_e0dbc3751d359960] reader_t
        | Construct of (ro, Node.t, array_t) Capnp.Array.t
        | NullPtrLit
        | Undefined of int
      val get : t -> unnamed_union_t
      val of_message : 'cap message_t -> t
      val of_builder : struct_t builder_t -> t
    end
    module TU : sig
      type struct_t = [`TU_c63033d95787d2ff]
      type t = struct_t reader_t
      module FileEntry : sig
        type struct_t = [`FileEntry_8f25ab49a7ca891f]
        type t = struct_t reader_t
        val fd_get : t -> int
        val has_name : t -> bool
        val name_get : t -> string
        val of_message : 'cap message_t -> t
        val of_builder : struct_t builder_t -> t
      end
      val has_decls : t -> bool
      val decls_get : t -> (ro, Node.t, array_t) Capnp.Array.t
      val decls_get_list : t -> Node.t list
      val decls_get_array : t -> Node.t array
      val has_files : t -> bool
      val files_get : t -> (ro, [`FileEntry_8f25ab49a7ca891f] reader_t, array_t) Capnp.Array.t
      val files_get_list : t -> [`FileEntry_8f25ab49a7ca891f] reader_t list
      val files_get_array : t -> [`FileEntry_8f25ab49a7ca891f] reader_t array
      val of_message : 'cap message_t -> t
      val of_builder : struct_t builder_t -> t
    end
    module Err : sig
      type struct_t = [`Err_9162b284a3cba818]
      type t = struct_t reader_t
      val has_loc : t -> bool
      val loc_get : t -> Loc.t
      val loc_get_pipelined : struct_t MessageWrapper.StructRef.t -> Loc.struct_t MessageWrapper.StructRef.t
      val has_reason : t -> bool
      val reason_get : t -> string
      val of_message : 'cap message_t -> t
      val of_builder : struct_t builder_t -> t
    end
    module SerResult : sig
      type struct_t = [`SerResult_a5cc2b3709c2654d]
      type t = struct_t reader_t
      type unnamed_union_t =
        | Ok
        | Err
        | Undefined of int
      val get : t -> unnamed_union_t
      val of_message : 'cap message_t -> t
      val of_builder : struct_t builder_t -> t
    end
  end

  module Builder : sig
    type array_t = Reader.builder_array_t
    type reader_array_t = Reader.array_t
    type pointer_t = rw MessageWrapper.Slice.t
    module Loc : sig
      type struct_t = [`Loc_b1436df23fb200b4]
      type t = struct_t builder_t
      module SrcPos : sig
        type struct_t = [`SrcPos_80bc3ef5a3c049a0]
        type t = struct_t builder_t
        val l_get : t -> int
        val l_set_exn : t -> int -> unit
        val c_get : t -> int
        val c_set_exn : t -> int -> unit
        val fd_get : t -> int
        val fd_set_exn : t -> int -> unit
        val of_message : rw message_t -> t
        val to_message : t -> rw message_t
        val to_reader : t -> struct_t reader_t
        val init_root : ?message_size:int -> unit -> t
        val init_pointer : pointer_t -> t
      end
      val has_start : t -> bool
      val start_get : t -> [`SrcPos_80bc3ef5a3c049a0] builder_t
      val start_set_reader : t -> [`SrcPos_80bc3ef5a3c049a0] reader_t -> [`SrcPos_80bc3ef5a3c049a0] builder_t
      val start_set_builder : t -> [`SrcPos_80bc3ef5a3c049a0] builder_t -> [`SrcPos_80bc3ef5a3c049a0] builder_t
      val start_init : t -> [`SrcPos_80bc3ef5a3c049a0] builder_t
      val has_end : t -> bool
      val end_get : t -> [`SrcPos_80bc3ef5a3c049a0] builder_t
      val end_set_reader : t -> [`SrcPos_80bc3ef5a3c049a0] reader_t -> [`SrcPos_80bc3ef5a3c049a0] builder_t
      val end_set_builder : t -> [`SrcPos_80bc3ef5a3c049a0] builder_t -> [`SrcPos_80bc3ef5a3c049a0] builder_t
      val end_init : t -> [`SrcPos_80bc3ef5a3c049a0] builder_t
      val of_message : rw message_t -> t
      val to_message : t -> rw message_t
      val to_reader : t -> struct_t reader_t
      val init_root : ?message_size:int -> unit -> t
      val init_pointer : pointer_t -> t
    end
    module Node : sig
      type struct_t = [`Node_e2a8b78aa50d684a]
      type t = struct_t builder_t
      val has_loc : t -> bool
      val loc_get : t -> Loc.t
      val loc_set_reader : t -> Loc.struct_t reader_t -> Loc.t
      val loc_set_builder : t -> Loc.t -> Loc.t
      val loc_init : t -> Loc.t
      val desc_get : t -> pointer_t
      val desc_get_interface : t -> 'a MessageWrapper.Capability.t option
      val desc_set : t -> pointer_t -> pointer_t
      val desc_set_reader : t -> Reader.pointer_t -> pointer_t
      val desc_set_interface : t -> 'a MessageWrapper.Capability.t option -> unit
      val of_message : rw message_t -> t
      val to_message : t -> rw message_t
      val to_reader : t -> struct_t reader_t
      val init_root : ?message_size:int -> unit -> t
      val init_pointer : pointer_t -> t
    end
    module Type : sig
      type struct_t = [`Type_f4d8929c89991d82]
      type t = struct_t builder_t
      module BuiltinKind : sig
        type t = BuiltinKind_11913544707969661485.t =
          | Char
          | UChar
          | Short
          | UShort
          | Void
          | Bool
          | Int
          | UInt
          | Long
          | ULong
          | LongLong
          | ULongLong
          | Undefined of int
      end
      module Record : sig
        type struct_t = [`Record_f92013bb699d0281]
        type t = struct_t builder_t
        val kind_get : t -> RecordKind_12907431634679073908.t
        val kind_set : t -> RecordKind_12907431634679073908.t -> unit
        val kind_set_unsafe : t -> RecordKind_12907431634679073908.t -> unit
        val has_name : t -> bool
        val name_get : t -> string
        val name_set : t -> string -> unit
        val of_message : rw message_t -> t
        val to_message : t -> rw message_t
        val to_reader : t -> struct_t reader_t
        val init_root : ?message_size:int -> unit -> t
        val init_pointer : pointer_t -> t
      end
      type unnamed_union_t =
        | Builtin of BuiltinKind_11913544707969661485.t
        | Pointer of [`Type_f4d8929c89991d82] builder_t
        | PointerLoc of Node.t
        | Record of [`Record_f92013bb699d0281] builder_t
        | EnumType of string
        | Undefined of int
      val get : t -> unnamed_union_t
      val builtin_set : t -> BuiltinKind_11913544707969661485.t -> unit
      val builtin_set_unsafe : t -> BuiltinKind_11913544707969661485.t -> unit
      val pointer_set_reader : t -> [`Type_f4d8929c89991d82] reader_t -> [`Type_f4d8929c89991d82] builder_t
      val pointer_set_builder : t -> [`Type_f4d8929c89991d82] builder_t -> [`Type_f4d8929c89991d82] builder_t
      val pointer_init : t -> [`Type_f4d8929c89991d82] builder_t
      val pointer_loc_set_reader : t -> Node.struct_t reader_t -> Node.t
      val pointer_loc_set_builder : t -> Node.t -> Node.t
      val pointer_loc_init : t -> Node.t
      val record_set_reader : t -> [`Record_f92013bb699d0281] reader_t -> [`Record_f92013bb699d0281] builder_t
      val record_set_builder : t -> [`Record_f92013bb699d0281] builder_t -> [`Record_f92013bb699d0281] builder_t
      val record_init : t -> [`Record_f92013bb699d0281] builder_t
      val enum_type_set : t -> string -> unit
      val of_message : rw message_t -> t
      val to_message : t -> rw message_t
      val to_reader : t -> struct_t reader_t
      val init_root : ?message_size:int -> unit -> t
      val init_pointer : pointer_t -> t
    end
    module Stmt : sig
      type struct_t = [`Stmt_f6a0f771ad50816c]
      type t = struct_t builder_t
      module Return : sig
        type struct_t = [`Return_fe7af58e3af28b84]
        type t = struct_t builder_t
        val has_expr : t -> bool
        val expr_get : t -> Node.t
        val expr_set_reader : t -> Node.struct_t reader_t -> Node.t
        val expr_set_builder : t -> Node.t -> Node.t
        val expr_init : t -> Node.t
        val of_message : rw message_t -> t
        val to_message : t -> rw message_t
        val to_reader : t -> struct_t reader_t
        val init_root : ?message_size:int -> unit -> t
        val init_pointer : pointer_t -> t
      end
      module If : sig
        type struct_t = [`If_bfef959001088175]
        type t = struct_t builder_t
        val has_cond : t -> bool
        val cond_get : t -> Node.t
        val cond_set_reader : t -> Node.struct_t reader_t -> Node.t
        val cond_set_builder : t -> Node.t -> Node.t
        val cond_init : t -> Node.t
        val has_then : t -> bool
        val then_get : t -> Node.t
        val then_set_reader : t -> Node.struct_t reader_t -> Node.t
        val then_set_builder : t -> Node.t -> Node.t
        val then_init : t -> Node.t
        val has_else : t -> bool
        val else_get : t -> Node.t
        val else_set_reader : t -> Node.struct_t reader_t -> Node.t
        val else_set_builder : t -> Node.t -> Node.t
        val else_init : t -> Node.t
        val of_message : rw message_t -> t
        val to_message : t -> rw message_t
        val to_reader : t -> struct_t reader_t
        val init_root : ?message_size:int -> unit -> t
        val init_pointer : pointer_t -> t
      end
      module Compound : sig
        type struct_t = [`Compound_899b868295a7b9ce]
        type t = struct_t builder_t
        val has_stmts : t -> bool
        val stmts_get : t -> (rw, Node.t, array_t) Capnp.Array.t
        val stmts_get_list : t -> Node.t list
        val stmts_get_array : t -> Node.t array
        val stmts_set : t -> (rw, Node.t, array_t) Capnp.Array.t -> (rw, Node.t, array_t) Capnp.Array.t
        val stmts_set_list : t -> Node.t list -> (rw, Node.t, array_t) Capnp.Array.t
        val stmts_set_array : t -> Node.t array -> (rw, Node.t, array_t) Capnp.Array.t
        val stmts_init : t -> int -> (rw, Node.t, array_t) Capnp.Array.t
        val has_r_brace : t -> bool
        val r_brace_get : t -> Loc.t
        val r_brace_set_reader : t -> Loc.struct_t reader_t -> Loc.t
        val r_brace_set_builder : t -> Loc.t -> Loc.t
        val r_brace_init : t -> Loc.t
        val of_message : rw message_t -> t
        val to_message : t -> rw message_t
        val to_reader : t -> struct_t reader_t
        val init_root : ?message_size:int -> unit -> t
        val init_pointer : pointer_t -> t
      end
      module While : sig
        type struct_t = [`While_ef7716d0539edb37]
        type t = struct_t builder_t
        val has_cond : t -> bool
        val cond_get : t -> Node.t
        val cond_set_reader : t -> Node.struct_t reader_t -> Node.t
        val cond_set_builder : t -> Node.t -> Node.t
        val cond_init : t -> Node.t
        val has_body : t -> bool
        val body_get : t -> Node.t
        val body_set_reader : t -> Node.struct_t reader_t -> Node.t
        val body_set_builder : t -> Node.t -> Node.t
        val body_init : t -> Node.t
        val has_spec : t -> bool
        val spec_get : t -> (rw, [`Clause_adb9aafdab430c1d] builder_t, array_t) Capnp.Array.t
        val spec_get_list : t -> [`Clause_adb9aafdab430c1d] builder_t list
        val spec_get_array : t -> [`Clause_adb9aafdab430c1d] builder_t array
        val spec_set : t -> (rw, [`Clause_adb9aafdab430c1d] builder_t, array_t) Capnp.Array.t -> (rw, [`Clause_adb9aafdab430c1d] builder_t, array_t) Capnp.Array.t
        val spec_set_list : t -> [`Clause_adb9aafdab430c1d] builder_t list -> (rw, [`Clause_adb9aafdab430c1d] builder_t, array_t) Capnp.Array.t
        val spec_set_array : t -> [`Clause_adb9aafdab430c1d] builder_t array -> (rw, [`Clause_adb9aafdab430c1d] builder_t, array_t) Capnp.Array.t
        val spec_init : t -> int -> (rw, [`Clause_adb9aafdab430c1d] builder_t, array_t) Capnp.Array.t
        val has_while_loc : t -> bool
        val while_loc_get : t -> Loc.t
        val while_loc_set_reader : t -> Loc.struct_t reader_t -> Loc.t
        val while_loc_set_builder : t -> Loc.t -> Loc.t
        val while_loc_init : t -> Loc.t
        val of_message : rw message_t -> t
        val to_message : t -> rw message_t
        val to_reader : t -> struct_t reader_t
        val init_root : ?message_size:int -> unit -> t
        val init_pointer : pointer_t -> t
      end
      module Case : sig
        type struct_t = [`Case_d41d9dffe36da558]
        type t = struct_t builder_t
        val has_lhs : t -> bool
        val lhs_get : t -> Node.t
        val lhs_set_reader : t -> Node.struct_t reader_t -> Node.t
        val lhs_set_builder : t -> Node.t -> Node.t
        val lhs_init : t -> Node.t
        val has_stmt : t -> bool
        val stmt_get : t -> Node.t
        val stmt_set_reader : t -> Node.struct_t reader_t -> Node.t
        val stmt_set_builder : t -> Node.t -> Node.t
        val stmt_init : t -> Node.t
        val of_message : rw message_t -> t
        val to_message : t -> rw message_t
        val to_reader : t -> struct_t reader_t
        val init_root : ?message_size:int -> unit -> t
        val init_pointer : pointer_t -> t
      end
      module DefCase : sig
        type struct_t = [`DefCase_ef0bcc479ff59f3e]
        type t = struct_t builder_t
        val has_stmt : t -> bool
        val stmt_get : t -> Node.t
        val stmt_set_reader : t -> Node.struct_t reader_t -> Node.t
        val stmt_set_builder : t -> Node.t -> Node.t
        val stmt_init : t -> Node.t
        val of_message : rw message_t -> t
        val to_message : t -> rw message_t
        val to_reader : t -> struct_t reader_t
        val init_root : ?message_size:int -> unit -> t
        val init_pointer : pointer_t -> t
      end
      module Switch : sig
        type struct_t = [`Switch_ffc6828955aafac4]
        type t = struct_t builder_t
        val has_cond : t -> bool
        val cond_get : t -> Node.t
        val cond_set_reader : t -> Node.struct_t reader_t -> Node.t
        val cond_set_builder : t -> Node.t -> Node.t
        val cond_init : t -> Node.t
        val has_cases : t -> bool
        val cases_get : t -> (rw, Node.t, array_t) Capnp.Array.t
        val cases_get_list : t -> Node.t list
        val cases_get_array : t -> Node.t array
        val cases_set : t -> (rw, Node.t, array_t) Capnp.Array.t -> (rw, Node.t, array_t) Capnp.Array.t
        val cases_set_list : t -> Node.t list -> (rw, Node.t, array_t) Capnp.Array.t
        val cases_set_array : t -> Node.t array -> (rw, Node.t, array_t) Capnp.Array.t
        val cases_init : t -> int -> (rw, Node.t, array_t) Capnp.Array.t
        val of_message : rw message_t -> t
        val to_message : t -> rw message_t
        val to_reader : t -> struct_t reader_t
        val init_root : ?message_size:int -> unit -> t
        val init_pointer : pointer_t -> t
      end
      type unnamed_union_t =
        | UnionNotInitialized
        | Ann of string
        | Decl of (rw, Node.t, array_t) Capnp.Array.t
        | Compound of [`Compound_899b868295a7b9ce] builder_t
        | Expr of Node.t
        | Return of [`Return_fe7af58e3af28b84] builder_t
        | If of [`If_bfef959001088175] builder_t
        | Null
        | While of [`While_ef7716d0539edb37] builder_t
        | DoWhile of [`While_ef7716d0539edb37] builder_t
        | Break
        | Continue
        | Switch of [`Switch_ffc6828955aafac4] builder_t
        | Case of [`Case_d41d9dffe36da558] builder_t
        | DefCase of [`DefCase_ef0bcc479ff59f3e] builder_t
        | Undefined of int
      val get : t -> unnamed_union_t
      val union_not_initialized_set : t -> unit
      val ann_set : t -> string -> unit
      val decl_set : t -> (rw, Node.t, array_t) Capnp.Array.t -> (rw, Node.t, array_t) Capnp.Array.t
      val decl_set_list : t -> Node.t list -> (rw, Node.t, array_t) Capnp.Array.t
      val decl_set_array : t -> Node.t array -> (rw, Node.t, array_t) Capnp.Array.t
      val decl_init : t -> int -> (rw, Node.t, array_t) Capnp.Array.t
      val compound_set_reader : t -> [`Compound_899b868295a7b9ce] reader_t -> [`Compound_899b868295a7b9ce] builder_t
      val compound_set_builder : t -> [`Compound_899b868295a7b9ce] builder_t -> [`Compound_899b868295a7b9ce] builder_t
      val compound_init : t -> [`Compound_899b868295a7b9ce] builder_t
      val expr_set_reader : t -> Node.struct_t reader_t -> Node.t
      val expr_set_builder : t -> Node.t -> Node.t
      val expr_init : t -> Node.t
      val return_set_reader : t -> [`Return_fe7af58e3af28b84] reader_t -> [`Return_fe7af58e3af28b84] builder_t
      val return_set_builder : t -> [`Return_fe7af58e3af28b84] builder_t -> [`Return_fe7af58e3af28b84] builder_t
      val return_init : t -> [`Return_fe7af58e3af28b84] builder_t
      val if_set_reader : t -> [`If_bfef959001088175] reader_t -> [`If_bfef959001088175] builder_t
      val if_set_builder : t -> [`If_bfef959001088175] builder_t -> [`If_bfef959001088175] builder_t
      val if_init : t -> [`If_bfef959001088175] builder_t
      val null_set : t -> unit
      val while_set_reader : t -> [`While_ef7716d0539edb37] reader_t -> [`While_ef7716d0539edb37] builder_t
      val while_set_builder : t -> [`While_ef7716d0539edb37] builder_t -> [`While_ef7716d0539edb37] builder_t
      val while_init : t -> [`While_ef7716d0539edb37] builder_t
      val do_while_set_reader : t -> [`While_ef7716d0539edb37] reader_t -> [`While_ef7716d0539edb37] builder_t
      val do_while_set_builder : t -> [`While_ef7716d0539edb37] builder_t -> [`While_ef7716d0539edb37] builder_t
      val do_while_init : t -> [`While_ef7716d0539edb37] builder_t
      val break_set : t -> unit
      val continue_set : t -> unit
      val switch_set_reader : t -> [`Switch_ffc6828955aafac4] reader_t -> [`Switch_ffc6828955aafac4] builder_t
      val switch_set_builder : t -> [`Switch_ffc6828955aafac4] builder_t -> [`Switch_ffc6828955aafac4] builder_t
      val switch_init : t -> [`Switch_ffc6828955aafac4] builder_t
      val case_set_reader : t -> [`Case_d41d9dffe36da558] reader_t -> [`Case_d41d9dffe36da558] builder_t
      val case_set_builder : t -> [`Case_d41d9dffe36da558] builder_t -> [`Case_d41d9dffe36da558] builder_t
      val case_init : t -> [`Case_d41d9dffe36da558] builder_t
      val def_case_set_reader : t -> [`DefCase_ef0bcc479ff59f3e] reader_t -> [`DefCase_ef0bcc479ff59f3e] builder_t
      val def_case_set_builder : t -> [`DefCase_ef0bcc479ff59f3e] builder_t -> [`DefCase_ef0bcc479ff59f3e] builder_t
      val def_case_init : t -> [`DefCase_ef0bcc479ff59f3e] builder_t
      val of_message : rw message_t -> t
      val to_message : t -> rw message_t
      val to_reader : t -> struct_t reader_t
      val init_root : ?message_size:int -> unit -> t
      val init_pointer : pointer_t -> t
    end
    module Clause : sig
      type struct_t = [`Clause_adb9aafdab430c1d]
      type t = struct_t builder_t
      val has_loc : t -> bool
      val loc_get : t -> Loc.t
      val loc_set_reader : t -> Loc.struct_t reader_t -> Loc.t
      val loc_set_builder : t -> Loc.t -> Loc.t
      val loc_init : t -> Loc.t
      val has_text : t -> bool
      val text_get : t -> string
      val text_set : t -> string -> unit
      val of_message : rw message_t -> t
      val to_message : t -> rw message_t
      val to_reader : t -> struct_t reader_t
      val init_root : ?message_size:int -> unit -> t
      val init_pointer : pointer_t -> t
    end
    module RecordKind : sig
      type t = RecordKind_12907431634679073908.t =
        | Struc
        | Class
        | Unio
        | Undefined of int
    end
    module Decl : sig
      type struct_t = [`Decl_d96c7f8624e22938]
      type t = struct_t builder_t
      module Param : sig
        type struct_t = [`Param_97bce41c55c2994a]
        type t = struct_t builder_t
        val has_type : t -> bool
        val type_get : t -> Node.t
        val type_set_reader : t -> Node.struct_t reader_t -> Node.t
        val type_set_builder : t -> Node.t -> Node.t
        val type_init : t -> Node.t
        val has_name : t -> bool
        val name_get : t -> string
        val name_set : t -> string -> unit
        val has_default : t -> bool
        val default_get : t -> Node.t
        val default_set_reader : t -> Node.struct_t reader_t -> Node.t
        val default_set_builder : t -> Node.t -> Node.t
        val default_init : t -> Node.t
        val of_message : rw message_t -> t
        val to_message : t -> rw message_t
        val to_reader : t -> struct_t reader_t
        val init_root : ?message_size:int -> unit -> t
        val init_pointer : pointer_t -> t
      end
      module Var : sig
        type struct_t = [`Var_8da2907bb130c41c]
        type t = struct_t builder_t
        module InitStyle : sig
          type t = InitStyle_15285372864656172726.t =
            | CInit
            | CallInit
            | ListInit
            | Undefined of int
        end
        module VarInit : sig
          type struct_t = [`VarInit_96ff0430cb165092]
          type t = struct_t builder_t
          val has_init : t -> bool
          val init_get : t -> Node.t
          val init_set_reader : t -> Node.struct_t reader_t -> Node.t
          val init_set_builder : t -> Node.t -> Node.t
          val init_init : t -> Node.t
          val style_get : t -> InitStyle.t
          val style_set : t -> InitStyle.t -> unit
          val style_set_unsafe : t -> InitStyle.t -> unit
          val of_message : rw message_t -> t
          val to_message : t -> rw message_t
          val to_reader : t -> struct_t reader_t
          val init_root : ?message_size:int -> unit -> t
          val init_pointer : pointer_t -> t
        end
        val has_name : t -> bool
        val name_get : t -> string
        val name_set : t -> string -> unit
        val has_type : t -> bool
        val type_get : t -> Node.t
        val type_set_reader : t -> Node.struct_t reader_t -> Node.t
        val type_set_builder : t -> Node.t -> Node.t
        val type_init : t -> Node.t
        val has_init : t -> bool
        val init_get : t -> [`VarInit_96ff0430cb165092] builder_t
        val init_set_reader : t -> [`VarInit_96ff0430cb165092] reader_t -> [`VarInit_96ff0430cb165092] builder_t
        val init_set_builder : t -> [`VarInit_96ff0430cb165092] builder_t -> [`VarInit_96ff0430cb165092] builder_t
        val init_init : t -> [`VarInit_96ff0430cb165092] builder_t
        val of_message : rw message_t -> t
        val to_message : t -> rw message_t
        val to_reader : t -> struct_t reader_t
        val init_root : ?message_size:int -> unit -> t
        val init_pointer : pointer_t -> t
      end
      module Function : sig
        type struct_t = [`Function_d64c65470b140c81]
        type t = struct_t builder_t
        val has_name : t -> bool
        val name_get : t -> string
        val name_set : t -> string -> unit
        val has_body : t -> bool
        val body_get : t -> Node.t
        val body_set_reader : t -> Node.struct_t reader_t -> Node.t
        val body_set_builder : t -> Node.t -> Node.t
        val body_init : t -> Node.t
        val has_result : t -> bool
        val result_get : t -> Node.t
        val result_set_reader : t -> Node.struct_t reader_t -> Node.t
        val result_set_builder : t -> Node.t -> Node.t
        val result_init : t -> Node.t
        val has_params : t -> bool
        val params_get : t -> (rw, Param.t, array_t) Capnp.Array.t
        val params_get_list : t -> Param.t list
        val params_get_array : t -> Param.t array
        val params_set : t -> (rw, Param.t, array_t) Capnp.Array.t -> (rw, Param.t, array_t) Capnp.Array.t
        val params_set_list : t -> Param.t list -> (rw, Param.t, array_t) Capnp.Array.t
        val params_set_array : t -> Param.t array -> (rw, Param.t, array_t) Capnp.Array.t
        val params_init : t -> int -> (rw, Param.t, array_t) Capnp.Array.t
        val has_contract : t -> bool
        val contract_get : t -> (rw, Clause.t, array_t) Capnp.Array.t
        val contract_get_list : t -> Clause.t list
        val contract_get_array : t -> Clause.t array
        val contract_set : t -> (rw, Clause.t, array_t) Capnp.Array.t -> (rw, Clause.t, array_t) Capnp.Array.t
        val contract_set_list : t -> Clause.t list -> (rw, Clause.t, array_t) Capnp.Array.t
        val contract_set_array : t -> Clause.t array -> (rw, Clause.t, array_t) Capnp.Array.t
        val contract_init : t -> int -> (rw, Clause.t, array_t) Capnp.Array.t
        val of_message : rw message_t -> t
        val to_message : t -> rw message_t
        val to_reader : t -> struct_t reader_t
        val init_root : ?message_size:int -> unit -> t
        val init_pointer : pointer_t -> t
      end
      module Field : sig
        type struct_t = [`Field_ca43d1968400194b]
        type t = struct_t builder_t
        module InitStyle : sig
          type t = InitStyle_13739150215916644662.t =
            | CopyInit
            | ListInit
            | Undefined of int
        end
        module FieldInit : sig
          type struct_t = [`FieldInit_91afac6d2dc82432]
          type t = struct_t builder_t
          val has_init : t -> bool
          val init_get : t -> Node.t
          val init_set_reader : t -> Node.struct_t reader_t -> Node.t
          val init_set_builder : t -> Node.t -> Node.t
          val init_init : t -> Node.t
          val style_get : t -> InitStyle.t
          val style_set : t -> InitStyle.t -> unit
          val style_set_unsafe : t -> InitStyle.t -> unit
          val of_message : rw message_t -> t
          val to_message : t -> rw message_t
          val to_reader : t -> struct_t reader_t
          val init_root : ?message_size:int -> unit -> t
          val init_pointer : pointer_t -> t
        end
        val has_name : t -> bool
        val name_get : t -> string
        val name_set : t -> string -> unit
        val has_type : t -> bool
        val type_get : t -> Node.t
        val type_set_reader : t -> Node.struct_t reader_t -> Node.t
        val type_set_builder : t -> Node.t -> Node.t
        val type_init : t -> Node.t
        val has_init : t -> bool
        val init_get : t -> [`FieldInit_91afac6d2dc82432] builder_t
        val init_set_reader : t -> [`FieldInit_91afac6d2dc82432] reader_t -> [`FieldInit_91afac6d2dc82432] builder_t
        val init_set_builder : t -> [`FieldInit_91afac6d2dc82432] builder_t -> [`FieldInit_91afac6d2dc82432] builder_t
        val init_init : t -> [`FieldInit_91afac6d2dc82432] builder_t
        val of_message : rw message_t -> t
        val to_message : t -> rw message_t
        val to_reader : t -> struct_t reader_t
        val init_root : ?message_size:int -> unit -> t
        val init_pointer : pointer_t -> t
      end
      module Record : sig
        type struct_t = [`Record_c925b09644ce72d3]
        type t = struct_t builder_t
        val has_name : t -> bool
        val name_get : t -> string
        val name_set : t -> string -> unit
        val kind_get : t -> RecordKind.t
        val kind_set : t -> RecordKind.t -> unit
        val kind_set_unsafe : t -> RecordKind.t -> unit
        val has_fields : t -> bool
        val fields_get : t -> (rw, Node.t, array_t) Capnp.Array.t
        val fields_get_list : t -> Node.t list
        val fields_get_array : t -> Node.t array
        val fields_set : t -> (rw, Node.t, array_t) Capnp.Array.t -> (rw, Node.t, array_t) Capnp.Array.t
        val fields_set_list : t -> Node.t list -> (rw, Node.t, array_t) Capnp.Array.t
        val fields_set_array : t -> Node.t array -> (rw, Node.t, array_t) Capnp.Array.t
        val fields_init : t -> int -> (rw, Node.t, array_t) Capnp.Array.t
        val has_methods : t -> bool
        val methods_get : t -> (rw, Node.t, array_t) Capnp.Array.t
        val methods_get_list : t -> Node.t list
        val methods_get_array : t -> Node.t array
        val methods_set : t -> (rw, Node.t, array_t) Capnp.Array.t -> (rw, Node.t, array_t) Capnp.Array.t
        val methods_set_list : t -> Node.t list -> (rw, Node.t, array_t) Capnp.Array.t
        val methods_set_array : t -> Node.t array -> (rw, Node.t, array_t) Capnp.Array.t
        val methods_init : t -> int -> (rw, Node.t, array_t) Capnp.Array.t
        val has_def_get : t -> bool
        val has_def_set : t -> bool -> unit
        val has_decls : t -> bool
        val decls_get : t -> (rw, Node.t, array_t) Capnp.Array.t
        val decls_get_list : t -> Node.t list
        val decls_get_array : t -> Node.t array
        val decls_set : t -> (rw, Node.t, array_t) Capnp.Array.t -> (rw, Node.t, array_t) Capnp.Array.t
        val decls_set_list : t -> Node.t list -> (rw, Node.t, array_t) Capnp.Array.t
        val decls_set_array : t -> Node.t array -> (rw, Node.t, array_t) Capnp.Array.t
        val decls_init : t -> int -> (rw, Node.t, array_t) Capnp.Array.t
        val of_message : rw message_t -> t
        val to_message : t -> rw message_t
        val to_reader : t -> struct_t reader_t
        val init_root : ?message_size:int -> unit -> t
        val init_pointer : pointer_t -> t
      end
      module Method : sig
        type struct_t = [`Method_bebeef9161eb7d3c]
        type t = struct_t builder_t
        val static_get : t -> bool
        val static_set : t -> bool -> unit
        val has_func : t -> bool
        val func_get : t -> Function.t
        val func_set_reader : t -> Function.struct_t reader_t -> Function.t
        val func_set_builder : t -> Function.t -> Function.t
        val func_init : t -> Function.t
        val has_this : t -> bool
        val this_get : t -> Type.t
        val this_set_reader : t -> Type.struct_t reader_t -> Type.t
        val this_set_builder : t -> Type.t -> Type.t
        val this_init : t -> Type.t
        val of_message : rw message_t -> t
        val to_message : t -> rw message_t
        val to_reader : t -> struct_t reader_t
        val init_root : ?message_size:int -> unit -> t
        val init_pointer : pointer_t -> t
      end
      module Typedef : sig
        type struct_t = [`Typedef_e46ae190d3365bca]
        type t = struct_t builder_t
        val has_type : t -> bool
        val type_get : t -> Node.t
        val type_set_reader : t -> Node.struct_t reader_t -> Node.t
        val type_set_builder : t -> Node.t -> Node.t
        val type_init : t -> Node.t
        val has_name : t -> bool
        val name_get : t -> string
        val name_set : t -> string -> unit
        val of_message : rw message_t -> t
        val to_message : t -> rw message_t
        val to_reader : t -> struct_t reader_t
        val init_root : ?message_size:int -> unit -> t
        val init_pointer : pointer_t -> t
      end
      module Enum : sig
        type struct_t = [`Enum_daecdb4dcd868ea8]
        type t = struct_t builder_t
        module EnumField : sig
          type struct_t = [`EnumField_87676bdbadd4545d]
          type t = struct_t builder_t
          val has_name : t -> bool
          val name_get : t -> string
          val name_set : t -> string -> unit
          val has_expr : t -> bool
          val expr_get : t -> Node.t
          val expr_set_reader : t -> Node.struct_t reader_t -> Node.t
          val expr_set_builder : t -> Node.t -> Node.t
          val expr_init : t -> Node.t
          val of_message : rw message_t -> t
          val to_message : t -> rw message_t
          val to_reader : t -> struct_t reader_t
          val init_root : ?message_size:int -> unit -> t
          val init_pointer : pointer_t -> t
        end
        val has_name : t -> bool
        val name_get : t -> string
        val name_set : t -> string -> unit
        val has_fields : t -> bool
        val fields_get : t -> (rw, [`EnumField_87676bdbadd4545d] builder_t, array_t) Capnp.Array.t
        val fields_get_list : t -> [`EnumField_87676bdbadd4545d] builder_t list
        val fields_get_array : t -> [`EnumField_87676bdbadd4545d] builder_t array
        val fields_set : t -> (rw, [`EnumField_87676bdbadd4545d] builder_t, array_t) Capnp.Array.t -> (rw, [`EnumField_87676bdbadd4545d] builder_t, array_t) Capnp.Array.t
        val fields_set_list : t -> [`EnumField_87676bdbadd4545d] builder_t list -> (rw, [`EnumField_87676bdbadd4545d] builder_t, array_t) Capnp.Array.t
        val fields_set_array : t -> [`EnumField_87676bdbadd4545d] builder_t array -> (rw, [`EnumField_87676bdbadd4545d] builder_t, array_t) Capnp.Array.t
        val fields_init : t -> int -> (rw, [`EnumField_87676bdbadd4545d] builder_t, array_t) Capnp.Array.t
        val of_message : rw message_t -> t
        val to_message : t -> rw message_t
        val to_reader : t -> struct_t reader_t
        val init_root : ?message_size:int -> unit -> t
        val init_pointer : pointer_t -> t
      end
      type unnamed_union_t =
        | UnionNotInitialized
        | Ann of string
        | Empty
        | Var of [`Var_8da2907bb130c41c] builder_t
        | Function of [`Function_d64c65470b140c81] builder_t
        | Field of [`Field_ca43d1968400194b] builder_t
        | Record of [`Record_c925b09644ce72d3] builder_t
        | Method of [`Method_bebeef9161eb7d3c] builder_t
        | AccessSpec
        | DefDestructor
        | DefConstructor
        | Typedef of [`Typedef_e46ae190d3365bca] builder_t
        | EnumDecl of [`Enum_daecdb4dcd868ea8] builder_t
        | Undefined of int
      val get : t -> unnamed_union_t
      val union_not_initialized_set : t -> unit
      val ann_set : t -> string -> unit
      val empty_set : t -> unit
      val var_set_reader : t -> [`Var_8da2907bb130c41c] reader_t -> [`Var_8da2907bb130c41c] builder_t
      val var_set_builder : t -> [`Var_8da2907bb130c41c] builder_t -> [`Var_8da2907bb130c41c] builder_t
      val var_init : t -> [`Var_8da2907bb130c41c] builder_t
      val function_set_reader : t -> [`Function_d64c65470b140c81] reader_t -> [`Function_d64c65470b140c81] builder_t
      val function_set_builder : t -> [`Function_d64c65470b140c81] builder_t -> [`Function_d64c65470b140c81] builder_t
      val function_init : t -> [`Function_d64c65470b140c81] builder_t
      val field_set_reader : t -> [`Field_ca43d1968400194b] reader_t -> [`Field_ca43d1968400194b] builder_t
      val field_set_builder : t -> [`Field_ca43d1968400194b] builder_t -> [`Field_ca43d1968400194b] builder_t
      val field_init : t -> [`Field_ca43d1968400194b] builder_t
      val record_set_reader : t -> [`Record_c925b09644ce72d3] reader_t -> [`Record_c925b09644ce72d3] builder_t
      val record_set_builder : t -> [`Record_c925b09644ce72d3] builder_t -> [`Record_c925b09644ce72d3] builder_t
      val record_init : t -> [`Record_c925b09644ce72d3] builder_t
      val method_set_reader : t -> [`Method_bebeef9161eb7d3c] reader_t -> [`Method_bebeef9161eb7d3c] builder_t
      val method_set_builder : t -> [`Method_bebeef9161eb7d3c] builder_t -> [`Method_bebeef9161eb7d3c] builder_t
      val method_init : t -> [`Method_bebeef9161eb7d3c] builder_t
      val access_spec_set : t -> unit
      val def_destructor_set : t -> unit
      val def_constructor_set : t -> unit
      val typedef_set_reader : t -> [`Typedef_e46ae190d3365bca] reader_t -> [`Typedef_e46ae190d3365bca] builder_t
      val typedef_set_builder : t -> [`Typedef_e46ae190d3365bca] builder_t -> [`Typedef_e46ae190d3365bca] builder_t
      val typedef_init : t -> [`Typedef_e46ae190d3365bca] builder_t
      val enum_decl_set_reader : t -> [`Enum_daecdb4dcd868ea8] reader_t -> [`Enum_daecdb4dcd868ea8] builder_t
      val enum_decl_set_builder : t -> [`Enum_daecdb4dcd868ea8] builder_t -> [`Enum_daecdb4dcd868ea8] builder_t
      val enum_decl_init : t -> [`Enum_daecdb4dcd868ea8] builder_t
      val of_message : rw message_t -> t
      val to_message : t -> rw message_t
      val to_reader : t -> struct_t reader_t
      val init_root : ?message_size:int -> unit -> t
      val init_pointer : pointer_t -> t
    end
    module UnaryOpKind : sig
      type t = UnaryOpKind_16270584510146119878.t =
        | Plus
        | Minus
        | Not
        | LNot
        | AddrOf
        | Deref
        | PreInc
        | PreDec
        | PostInc
        | PostDec
        | Undefined of int
    end
    module BinaryOpKind : sig
      type t = BinaryOpKind_15775553773985184773.t =
        | Add
        | Sub
        | Assign
        | Mul
        | Div
        | Rem
        | Shl
        | Shr
        | Lt
        | Gt
        | Le
        | Ge
        | Eq
        | Ne
        | And
        | Or
        | Xor
        | LAnd
        | LOr
        | MulAssign
        | DivAssign
        | RemAssign
        | AddAssign
        | SubAssign
        | ShlAssign
        | ShrAssign
        | AndAssign
        | XorAssign
        | OrAssign
        | Undefined of int
    end
    module SufKind : sig
      type t = SufKind_10349718269051794478.t =
        | LSuf
        | LLSuf
        | NoSuf
        | Undefined of int
    end
    module NbBase : sig
      type t = NbBase_15750048951651279863.t =
        | Decimal
        | Octal
        | Hex
        | Undefined of int
    end
    module Expr : sig
      type struct_t = [`Expr_d5d009cc85c86562]
      type t = struct_t builder_t
      module UnaryOp : sig
        type struct_t = [`UnaryOp_b525d86a8f48e679]
        type t = struct_t builder_t
        val has_operand : t -> bool
        val operand_get : t -> Node.t
        val operand_set_reader : t -> Node.struct_t reader_t -> Node.t
        val operand_set_builder : t -> Node.t -> Node.t
        val operand_init : t -> Node.t
        val kind_get : t -> UnaryOpKind.t
        val kind_set : t -> UnaryOpKind.t -> unit
        val kind_set_unsafe : t -> UnaryOpKind.t -> unit
        val of_message : rw message_t -> t
        val to_message : t -> rw message_t
        val to_reader : t -> struct_t reader_t
        val init_root : ?message_size:int -> unit -> t
        val init_pointer : pointer_t -> t
      end
      module BinaryOp : sig
        type struct_t = [`BinaryOp_b95e9a5df08d277c]
        type t = struct_t builder_t
        val has_lhs : t -> bool
        val lhs_get : t -> Node.t
        val lhs_set_reader : t -> Node.struct_t reader_t -> Node.t
        val lhs_set_builder : t -> Node.t -> Node.t
        val lhs_init : t -> Node.t
        val has_rhs : t -> bool
        val rhs_get : t -> Node.t
        val rhs_set_reader : t -> Node.struct_t reader_t -> Node.t
        val rhs_set_builder : t -> Node.t -> Node.t
        val rhs_init : t -> Node.t
        val kind_get : t -> BinaryOpKind.t
        val kind_set : t -> BinaryOpKind.t -> unit
        val kind_set_unsafe : t -> BinaryOpKind.t -> unit
        val of_message : rw message_t -> t
        val to_message : t -> rw message_t
        val to_reader : t -> struct_t reader_t
        val init_root : ?message_size:int -> unit -> t
        val init_pointer : pointer_t -> t
      end
      module IntLit : sig
        type struct_t = [`IntLit_a21731ff472a9631]
        type t = struct_t builder_t
        val has_value : t -> bool
        val value_get : t -> string
        val value_set : t -> string -> unit
        val u_suffix_get : t -> bool
        val u_suffix_set : t -> bool -> unit
        val l_suffix_get : t -> SufKind.t
        val l_suffix_set : t -> SufKind.t -> unit
        val l_suffix_set_unsafe : t -> SufKind.t -> unit
        val base_get : t -> NbBase.t
        val base_set : t -> NbBase.t -> unit
        val base_set_unsafe : t -> NbBase.t -> unit
        val of_message : rw message_t -> t
        val to_message : t -> rw message_t
        val to_reader : t -> struct_t reader_t
        val init_root : ?message_size:int -> unit -> t
        val init_pointer : pointer_t -> t
      end
      module Call : sig
        type struct_t = [`Call_d6c567dfeede9b58]
        type t = struct_t builder_t
        val has_args : t -> bool
        val args_get : t -> (rw, Node.t, array_t) Capnp.Array.t
        val args_get_list : t -> Node.t list
        val args_get_array : t -> Node.t array
        val args_set : t -> (rw, Node.t, array_t) Capnp.Array.t -> (rw, Node.t, array_t) Capnp.Array.t
        val args_set_list : t -> Node.t list -> (rw, Node.t, array_t) Capnp.Array.t
        val args_set_array : t -> Node.t array -> (rw, Node.t, array_t) Capnp.Array.t
        val args_init : t -> int -> (rw, Node.t, array_t) Capnp.Array.t
        val has_callee : t -> bool
        val callee_get : t -> Node.t
        val callee_set_reader : t -> Node.struct_t reader_t -> Node.t
        val callee_set_builder : t -> Node.t -> Node.t
        val callee_init : t -> Node.t
        val of_message : rw message_t -> t
        val to_message : t -> rw message_t
        val to_reader : t -> struct_t reader_t
        val init_root : ?message_size:int -> unit -> t
        val init_pointer : pointer_t -> t
      end
      module Member : sig
        type struct_t = [`Member_ab509764d68e7721]
        type t = struct_t builder_t
        val has_base : t -> bool
        val base_get : t -> Node.t
        val base_set_reader : t -> Node.struct_t reader_t -> Node.t
        val base_set_builder : t -> Node.t -> Node.t
        val base_init : t -> Node.t
        val has_name : t -> bool
        val name_get : t -> string
        val name_set : t -> string -> unit
        val arrow_get : t -> bool
        val arrow_set : t -> bool -> unit
        val of_message : rw message_t -> t
        val to_message : t -> rw message_t
        val to_reader : t -> struct_t reader_t
        val init_root : ?message_size:int -> unit -> t
        val init_pointer : pointer_t -> t
      end
      module New : sig
        type struct_t = [`New_e0dbc3751d359960]
        type t = struct_t builder_t
        val has_type : t -> bool
        val type_get : t -> Type.t
        val type_set_reader : t -> Type.struct_t reader_t -> Type.t
        val type_set_builder : t -> Type.t -> Type.t
        val type_init : t -> Type.t
        val has_expr : t -> bool
        val expr_get : t -> Node.t
        val expr_set_reader : t -> Node.struct_t reader_t -> Node.t
        val expr_set_builder : t -> Node.t -> Node.t
        val expr_init : t -> Node.t
        val of_message : rw message_t -> t
        val to_message : t -> rw message_t
        val to_reader : t -> struct_t reader_t
        val init_root : ?message_size:int -> unit -> t
        val init_pointer : pointer_t -> t
      end
      type unnamed_union_t =
        | UnionNotInitialized
        | UnaryOp of [`UnaryOp_b525d86a8f48e679] builder_t
        | BinaryOp of [`BinaryOp_b95e9a5df08d277c] builder_t
        | BoolLit of bool
        | IntLit of [`IntLit_a21731ff472a9631] builder_t
        | StringLit of string
        | Call of [`Call_d6c567dfeede9b58] builder_t
        | DeclRef of string
        | Member of [`Member_ab509764d68e7721] builder_t
        | This
        | MemberCall of [`Call_d6c567dfeede9b58] builder_t
        | New of [`New_e0dbc3751d359960] builder_t
        | Construct of (rw, Node.t, array_t) Capnp.Array.t
        | NullPtrLit
        | Undefined of int
      val get : t -> unnamed_union_t
      val union_not_initialized_set : t -> unit
      val unary_op_set_reader : t -> [`UnaryOp_b525d86a8f48e679] reader_t -> [`UnaryOp_b525d86a8f48e679] builder_t
      val unary_op_set_builder : t -> [`UnaryOp_b525d86a8f48e679] builder_t -> [`UnaryOp_b525d86a8f48e679] builder_t
      val unary_op_init : t -> [`UnaryOp_b525d86a8f48e679] builder_t
      val binary_op_set_reader : t -> [`BinaryOp_b95e9a5df08d277c] reader_t -> [`BinaryOp_b95e9a5df08d277c] builder_t
      val binary_op_set_builder : t -> [`BinaryOp_b95e9a5df08d277c] builder_t -> [`BinaryOp_b95e9a5df08d277c] builder_t
      val binary_op_init : t -> [`BinaryOp_b95e9a5df08d277c] builder_t
      val bool_lit_set : t -> bool -> unit
      val int_lit_set_reader : t -> [`IntLit_a21731ff472a9631] reader_t -> [`IntLit_a21731ff472a9631] builder_t
      val int_lit_set_builder : t -> [`IntLit_a21731ff472a9631] builder_t -> [`IntLit_a21731ff472a9631] builder_t
      val int_lit_init : t -> [`IntLit_a21731ff472a9631] builder_t
      val string_lit_set : t -> string -> unit
      val call_set_reader : t -> [`Call_d6c567dfeede9b58] reader_t -> [`Call_d6c567dfeede9b58] builder_t
      val call_set_builder : t -> [`Call_d6c567dfeede9b58] builder_t -> [`Call_d6c567dfeede9b58] builder_t
      val call_init : t -> [`Call_d6c567dfeede9b58] builder_t
      val decl_ref_set : t -> string -> unit
      val member_set_reader : t -> [`Member_ab509764d68e7721] reader_t -> [`Member_ab509764d68e7721] builder_t
      val member_set_builder : t -> [`Member_ab509764d68e7721] builder_t -> [`Member_ab509764d68e7721] builder_t
      val member_init : t -> [`Member_ab509764d68e7721] builder_t
      val this_set : t -> unit
      val member_call_set_reader : t -> [`Call_d6c567dfeede9b58] reader_t -> [`Call_d6c567dfeede9b58] builder_t
      val member_call_set_builder : t -> [`Call_d6c567dfeede9b58] builder_t -> [`Call_d6c567dfeede9b58] builder_t
      val member_call_init : t -> [`Call_d6c567dfeede9b58] builder_t
      val new_set_reader : t -> [`New_e0dbc3751d359960] reader_t -> [`New_e0dbc3751d359960] builder_t
      val new_set_builder : t -> [`New_e0dbc3751d359960] builder_t -> [`New_e0dbc3751d359960] builder_t
      val new_init : t -> [`New_e0dbc3751d359960] builder_t
      val construct_set : t -> (rw, Node.t, array_t) Capnp.Array.t -> (rw, Node.t, array_t) Capnp.Array.t
      val construct_set_list : t -> Node.t list -> (rw, Node.t, array_t) Capnp.Array.t
      val construct_set_array : t -> Node.t array -> (rw, Node.t, array_t) Capnp.Array.t
      val construct_init : t -> int -> (rw, Node.t, array_t) Capnp.Array.t
      val null_ptr_lit_set : t -> unit
      val of_message : rw message_t -> t
      val to_message : t -> rw message_t
      val to_reader : t -> struct_t reader_t
      val init_root : ?message_size:int -> unit -> t
      val init_pointer : pointer_t -> t
    end
    module TU : sig
      type struct_t = [`TU_c63033d95787d2ff]
      type t = struct_t builder_t
      module FileEntry : sig
        type struct_t = [`FileEntry_8f25ab49a7ca891f]
        type t = struct_t builder_t
        val fd_get : t -> int
        val fd_set_exn : t -> int -> unit
        val has_name : t -> bool
        val name_get : t -> string
        val name_set : t -> string -> unit
        val of_message : rw message_t -> t
        val to_message : t -> rw message_t
        val to_reader : t -> struct_t reader_t
        val init_root : ?message_size:int -> unit -> t
        val init_pointer : pointer_t -> t
      end
      val has_decls : t -> bool
      val decls_get : t -> (rw, Node.t, array_t) Capnp.Array.t
      val decls_get_list : t -> Node.t list
      val decls_get_array : t -> Node.t array
      val decls_set : t -> (rw, Node.t, array_t) Capnp.Array.t -> (rw, Node.t, array_t) Capnp.Array.t
      val decls_set_list : t -> Node.t list -> (rw, Node.t, array_t) Capnp.Array.t
      val decls_set_array : t -> Node.t array -> (rw, Node.t, array_t) Capnp.Array.t
      val decls_init : t -> int -> (rw, Node.t, array_t) Capnp.Array.t
      val has_files : t -> bool
      val files_get : t -> (rw, [`FileEntry_8f25ab49a7ca891f] builder_t, array_t) Capnp.Array.t
      val files_get_list : t -> [`FileEntry_8f25ab49a7ca891f] builder_t list
      val files_get_array : t -> [`FileEntry_8f25ab49a7ca891f] builder_t array
      val files_set : t -> (rw, [`FileEntry_8f25ab49a7ca891f] builder_t, array_t) Capnp.Array.t -> (rw, [`FileEntry_8f25ab49a7ca891f] builder_t, array_t) Capnp.Array.t
      val files_set_list : t -> [`FileEntry_8f25ab49a7ca891f] builder_t list -> (rw, [`FileEntry_8f25ab49a7ca891f] builder_t, array_t) Capnp.Array.t
      val files_set_array : t -> [`FileEntry_8f25ab49a7ca891f] builder_t array -> (rw, [`FileEntry_8f25ab49a7ca891f] builder_t, array_t) Capnp.Array.t
      val files_init : t -> int -> (rw, [`FileEntry_8f25ab49a7ca891f] builder_t, array_t) Capnp.Array.t
      val of_message : rw message_t -> t
      val to_message : t -> rw message_t
      val to_reader : t -> struct_t reader_t
      val init_root : ?message_size:int -> unit -> t
      val init_pointer : pointer_t -> t
    end
    module Err : sig
      type struct_t = [`Err_9162b284a3cba818]
      type t = struct_t builder_t
      val has_loc : t -> bool
      val loc_get : t -> Loc.t
      val loc_set_reader : t -> Loc.struct_t reader_t -> Loc.t
      val loc_set_builder : t -> Loc.t -> Loc.t
      val loc_init : t -> Loc.t
      val has_reason : t -> bool
      val reason_get : t -> string
      val reason_set : t -> string -> unit
      val of_message : rw message_t -> t
      val to_message : t -> rw message_t
      val to_reader : t -> struct_t reader_t
      val init_root : ?message_size:int -> unit -> t
      val init_pointer : pointer_t -> t
    end
    module SerResult : sig
      type struct_t = [`SerResult_a5cc2b3709c2654d]
      type t = struct_t builder_t
      type unnamed_union_t =
        | Ok
        | Err
        | Undefined of int
      val get : t -> unnamed_union_t
      val ok_set : t -> unit
      val err_set : t -> unit
      val of_message : rw message_t -> t
      val to_message : t -> rw message_t
      val to_reader : t -> struct_t reader_t
      val init_root : ?message_size:int -> unit -> t
      val init_pointer : pointer_t -> t
    end
  end
end

module MakeRPC(MessageWrapper : Capnp.RPC.S) = struct
  type 'a reader_t = 'a MessageWrapper.StructStorage.reader_t
  type 'a builder_t = 'a MessageWrapper.StructStorage.builder_t
  module CamlBytes = Bytes
  module DefaultsMessage_ = Capnp.BytesMessage

  let _builder_defaults_message =
    let message_segments = [
      Bytes.unsafe_of_string "\
      ";
    ] in
    DefaultsMessage_.Message.readonly
      (DefaultsMessage_.Message.of_storage message_segments)

  let invalid_msg = Capnp.Message.invalid_msg

  include Capnp.Runtime.BuilderInc.Make[@inlined](MessageWrapper)

  type 'cap message_t = 'cap MessageWrapper.Message.t

  module NbBase_15750048951651279863 = struct
    type t =
      | Decimal
      | Octal
      | Hex
      | Undefined of int
    let decode u16 = match u16 with
      | 0 -> Decimal
      | 1 -> Octal
      | 2 -> Hex
      | v -> Undefined v
    let encode_safe enum = match enum with
      | Decimal -> 0
      | Octal -> 1
      | Hex -> 2
      | Undefined x -> invalid_msg "Cannot encode undefined enum value."
    let encode_unsafe enum = match enum with
      | Decimal -> 0
      | Octal -> 1
      | Hex -> 2
      | Undefined x -> x
  end
  module SufKind_10349718269051794478 = struct
    type t =
      | LSuf
      | LLSuf
      | NoSuf
      | Undefined of int
    let decode u16 = match u16 with
      | 0 -> LSuf
      | 1 -> LLSuf
      | 2 -> NoSuf
      | v -> Undefined v
    let encode_safe enum = match enum with
      | LSuf -> 0
      | LLSuf -> 1
      | NoSuf -> 2
      | Undefined x -> invalid_msg "Cannot encode undefined enum value."
    let encode_unsafe enum = match enum with
      | LSuf -> 0
      | LLSuf -> 1
      | NoSuf -> 2
      | Undefined x -> x
  end
  module BinaryOpKind_15775553773985184773 = struct
    type t =
      | Add
      | Sub
      | Assign
      | Mul
      | Div
      | Rem
      | Shl
      | Shr
      | Lt
      | Gt
      | Le
      | Ge
      | Eq
      | Ne
      | And
      | Or
      | Xor
      | LAnd
      | LOr
      | MulAssign
      | DivAssign
      | RemAssign
      | AddAssign
      | SubAssign
      | ShlAssign
      | ShrAssign
      | AndAssign
      | XorAssign
      | OrAssign
      | Undefined of int
    let decode u16 = match u16 with
      | 0 -> Add
      | 1 -> Sub
      | 2 -> Assign
      | 3 -> Mul
      | 4 -> Div
      | 5 -> Rem
      | 6 -> Shl
      | 7 -> Shr
      | 8 -> Lt
      | 9 -> Gt
      | 10 -> Le
      | 11 -> Ge
      | 12 -> Eq
      | 13 -> Ne
      | 14 -> And
      | 15 -> Or
      | 16 -> Xor
      | 17 -> LAnd
      | 18 -> LOr
      | 19 -> MulAssign
      | 20 -> DivAssign
      | 21 -> RemAssign
      | 22 -> AddAssign
      | 23 -> SubAssign
      | 24 -> ShlAssign
      | 25 -> ShrAssign
      | 26 -> AndAssign
      | 27 -> XorAssign
      | 28 -> OrAssign
      | v -> Undefined v
    let encode_safe enum = match enum with
      | Add -> 0
      | Sub -> 1
      | Assign -> 2
      | Mul -> 3
      | Div -> 4
      | Rem -> 5
      | Shl -> 6
      | Shr -> 7
      | Lt -> 8
      | Gt -> 9
      | Le -> 10
      | Ge -> 11
      | Eq -> 12
      | Ne -> 13
      | And -> 14
      | Or -> 15
      | Xor -> 16
      | LAnd -> 17
      | LOr -> 18
      | MulAssign -> 19
      | DivAssign -> 20
      | RemAssign -> 21
      | AddAssign -> 22
      | SubAssign -> 23
      | ShlAssign -> 24
      | ShrAssign -> 25
      | AndAssign -> 26
      | XorAssign -> 27
      | OrAssign -> 28
      | Undefined x -> invalid_msg "Cannot encode undefined enum value."
    let encode_unsafe enum = match enum with
      | Add -> 0
      | Sub -> 1
      | Assign -> 2
      | Mul -> 3
      | Div -> 4
      | Rem -> 5
      | Shl -> 6
      | Shr -> 7
      | Lt -> 8
      | Gt -> 9
      | Le -> 10
      | Ge -> 11
      | Eq -> 12
      | Ne -> 13
      | And -> 14
      | Or -> 15
      | Xor -> 16
      | LAnd -> 17
      | LOr -> 18
      | MulAssign -> 19
      | DivAssign -> 20
      | RemAssign -> 21
      | AddAssign -> 22
      | SubAssign -> 23
      | ShlAssign -> 24
      | ShrAssign -> 25
      | AndAssign -> 26
      | XorAssign -> 27
      | OrAssign -> 28
      | Undefined x -> x
  end
  module UnaryOpKind_16270584510146119878 = struct
    type t =
      | Plus
      | Minus
      | Not
      | LNot
      | AddrOf
      | Deref
      | PreInc
      | PreDec
      | PostInc
      | PostDec
      | Undefined of int
    let decode u16 = match u16 with
      | 0 -> Plus
      | 1 -> Minus
      | 2 -> Not
      | 3 -> LNot
      | 4 -> AddrOf
      | 5 -> Deref
      | 6 -> PreInc
      | 7 -> PreDec
      | 8 -> PostInc
      | 9 -> PostDec
      | v -> Undefined v
    let encode_safe enum = match enum with
      | Plus -> 0
      | Minus -> 1
      | Not -> 2
      | LNot -> 3
      | AddrOf -> 4
      | Deref -> 5
      | PreInc -> 6
      | PreDec -> 7
      | PostInc -> 8
      | PostDec -> 9
      | Undefined x -> invalid_msg "Cannot encode undefined enum value."
    let encode_unsafe enum = match enum with
      | Plus -> 0
      | Minus -> 1
      | Not -> 2
      | LNot -> 3
      | AddrOf -> 4
      | Deref -> 5
      | PreInc -> 6
      | PreDec -> 7
      | PostInc -> 8
      | PostDec -> 9
      | Undefined x -> x
  end
  module InitStyle_13739150215916644662 = struct
    type t =
      | CopyInit
      | ListInit
      | Undefined of int
    let decode u16 = match u16 with
      | 0 -> CopyInit
      | 1 -> ListInit
      | v -> Undefined v
    let encode_safe enum = match enum with
      | CopyInit -> 0
      | ListInit -> 1
      | Undefined x -> invalid_msg "Cannot encode undefined enum value."
    let encode_unsafe enum = match enum with
      | CopyInit -> 0
      | ListInit -> 1
      | Undefined x -> x
  end
  module InitStyle_15285372864656172726 = struct
    type t =
      | CInit
      | CallInit
      | ListInit
      | Undefined of int
    let decode u16 = match u16 with
      | 0 -> CInit
      | 1 -> CallInit
      | 2 -> ListInit
      | v -> Undefined v
    let encode_safe enum = match enum with
      | CInit -> 0
      | CallInit -> 1
      | ListInit -> 2
      | Undefined x -> invalid_msg "Cannot encode undefined enum value."
    let encode_unsafe enum = match enum with
      | CInit -> 0
      | CallInit -> 1
      | ListInit -> 2
      | Undefined x -> x
  end
  module RecordKind_12907431634679073908 = struct
    type t =
      | Struc
      | Class
      | Unio
      | Undefined of int
    let decode u16 = match u16 with
      | 0 -> Struc
      | 1 -> Class
      | 2 -> Unio
      | v -> Undefined v
    let encode_safe enum = match enum with
      | Struc -> 0
      | Class -> 1
      | Unio -> 2
      | Undefined x -> invalid_msg "Cannot encode undefined enum value."
    let encode_unsafe enum = match enum with
      | Struc -> 0
      | Class -> 1
      | Unio -> 2
      | Undefined x -> x
  end
  module BuiltinKind_11913544707969661485 = struct
    type t =
      | Char
      | UChar
      | Short
      | UShort
      | Void
      | Bool
      | Int
      | UInt
      | Long
      | ULong
      | LongLong
      | ULongLong
      | Undefined of int
    let decode u16 = match u16 with
      | 0 -> Char
      | 1 -> UChar
      | 2 -> Short
      | 3 -> UShort
      | 4 -> Void
      | 5 -> Bool
      | 6 -> Int
      | 7 -> UInt
      | 8 -> Long
      | 9 -> ULong
      | 10 -> LongLong
      | 11 -> ULongLong
      | v -> Undefined v
    let encode_safe enum = match enum with
      | Char -> 0
      | UChar -> 1
      | Short -> 2
      | UShort -> 3
      | Void -> 4
      | Bool -> 5
      | Int -> 6
      | UInt -> 7
      | Long -> 8
      | ULong -> 9
      | LongLong -> 10
      | ULongLong -> 11
      | Undefined x -> invalid_msg "Cannot encode undefined enum value."
    let encode_unsafe enum = match enum with
      | Char -> 0
      | UChar -> 1
      | Short -> 2
      | UShort -> 3
      | Void -> 4
      | Bool -> 5
      | Int -> 6
      | UInt -> 7
      | Long -> 8
      | ULong -> 9
      | LongLong -> 10
      | ULongLong -> 11
      | Undefined x -> x
  end
  module DefaultsCopier_ =
    Capnp.Runtime.BuilderOps.Make(Capnp.BytesMessage)(MessageWrapper)

  let _reader_defaults_message =
    MessageWrapper.Message.create
      (DefaultsMessage_.Message.total_size _builder_defaults_message)


  module Reader = struct
    type array_t = ro MessageWrapper.ListStorage.t
    type builder_array_t = rw MessageWrapper.ListStorage.t
    type pointer_t = ro MessageWrapper.Slice.t option
    let of_pointer = RA_.deref_opt_struct_pointer

    module Loc = struct
      type struct_t = [`Loc_b1436df23fb200b4]
      type t = struct_t reader_t
      module SrcPos = struct
        type struct_t = [`SrcPos_80bc3ef5a3c049a0]
        type t = struct_t reader_t
        let l_get x =
          RA_.get_uint16 ~default:0 x 0
        let c_get x =
          RA_.get_uint16 ~default:0 x 2
        let fd_get x =
          RA_.get_uint16 ~default:0 x 4
        let of_message x = RA_.get_root_struct (RA_.Message.readonly x)
        let of_builder x = Some (RA_.StructStorage.readonly x)
      end
      let has_start x =
        RA_.has_field x 0
      let start_get x =
        RA_.get_struct x 0
      let start_get_pipelined x =
        MessageWrapper.Untyped.struct_field x 0
      let has_end x =
        RA_.has_field x 1
      let end_get x =
        RA_.get_struct x 1
      let end_get_pipelined x =
        MessageWrapper.Untyped.struct_field x 1
      let of_message x = RA_.get_root_struct (RA_.Message.readonly x)
      let of_builder x = Some (RA_.StructStorage.readonly x)
    end
    module Node = struct
      type struct_t = [`Node_e2a8b78aa50d684a]
      type t = struct_t reader_t
      let has_loc x =
        RA_.has_field x 0
      let loc_get x =
        RA_.get_struct x 0
      let loc_get_pipelined x =
        MessageWrapper.Untyped.struct_field x 0
      let desc_get x =
        RA_.get_pointer x 1
      let desc_get_interface x =
        RA_.get_interface x 1
      let of_message x = RA_.get_root_struct (RA_.Message.readonly x)
      let of_builder x = Some (RA_.StructStorage.readonly x)
    end
    module Type = struct
      type struct_t = [`Type_f4d8929c89991d82]
      type t = struct_t reader_t
      module BuiltinKind = struct
        type t = BuiltinKind_11913544707969661485.t =
          | Char
          | UChar
          | Short
          | UShort
          | Void
          | Bool
          | Int
          | UInt
          | Long
          | ULong
          | LongLong
          | ULongLong
          | Undefined of int
      end
      module Record = struct
        type struct_t = [`Record_f92013bb699d0281]
        type t = struct_t reader_t
        let kind_get x =
          let discr = RA_.get_uint16 ~default:0 x 0 in
          RecordKind_12907431634679073908.decode discr
        let has_name x =
          RA_.has_field x 0
        let name_get x =
          RA_.get_text ~default:"" x 0
        let of_message x = RA_.get_root_struct (RA_.Message.readonly x)
        let of_builder x = Some (RA_.StructStorage.readonly x)
      end
      let builtin_get x =
        let discr = RA_.get_uint16 ~default:0 x 0 in
        BuiltinKind_11913544707969661485.decode discr
      let has_pointer x =
        RA_.has_field x 0
      let pointer_get x =
        RA_.get_struct x 0
      let pointer_get_pipelined x =
        MessageWrapper.Untyped.struct_field x 0
      let has_pointer_loc x =
        RA_.has_field x 0
      let pointer_loc_get x =
        RA_.get_struct x 0
      let pointer_loc_get_pipelined x =
        MessageWrapper.Untyped.struct_field x 0
      let has_record x =
        RA_.has_field x 0
      let record_get x =
        RA_.get_struct x 0
      let record_get_pipelined x =
        MessageWrapper.Untyped.struct_field x 0
      let has_enum_type x =
        RA_.has_field x 0
      let enum_type_get x =
        RA_.get_text ~default:"" x 0
      type unnamed_union_t =
        | Builtin of BuiltinKind_11913544707969661485.t
        | Pointer of [`Type_f4d8929c89991d82] reader_t
        | PointerLoc of Node.t
        | Record of [`Record_f92013bb699d0281] reader_t
        | EnumType of string
        | Undefined of int
      let get x =
        match RA_.get_uint16 ~default:0 x 2 with
        | 0 -> Builtin (builtin_get x)
        | 1 -> Pointer (pointer_get x)
        | 2 -> PointerLoc (pointer_loc_get x)
        | 3 -> Record (record_get x)
        | 4 -> EnumType (enum_type_get x)
        | v -> Undefined v
      let of_message x = RA_.get_root_struct (RA_.Message.readonly x)
      let of_builder x = Some (RA_.StructStorage.readonly x)
    end
    module Stmt = struct
      type struct_t = [`Stmt_f6a0f771ad50816c]
      type t = struct_t reader_t
      module Return = struct
        type struct_t = [`Return_fe7af58e3af28b84]
        type t = struct_t reader_t
        let has_expr x =
          RA_.has_field x 0
        let expr_get x =
          RA_.get_struct x 0
        let expr_get_pipelined x =
          MessageWrapper.Untyped.struct_field x 0
        let of_message x = RA_.get_root_struct (RA_.Message.readonly x)
        let of_builder x = Some (RA_.StructStorage.readonly x)
      end
      module If = struct
        type struct_t = [`If_bfef959001088175]
        type t = struct_t reader_t
        let has_cond x =
          RA_.has_field x 0
        let cond_get x =
          RA_.get_struct x 0
        let cond_get_pipelined x =
          MessageWrapper.Untyped.struct_field x 0
        let has_then x =
          RA_.has_field x 1
        let then_get x =
          RA_.get_struct x 1
        let then_get_pipelined x =
          MessageWrapper.Untyped.struct_field x 1
        let has_else x =
          RA_.has_field x 2
        let else_get x =
          RA_.get_struct x 2
        let else_get_pipelined x =
          MessageWrapper.Untyped.struct_field x 2
        let of_message x = RA_.get_root_struct (RA_.Message.readonly x)
        let of_builder x = Some (RA_.StructStorage.readonly x)
      end
      module Compound = struct
        type struct_t = [`Compound_899b868295a7b9ce]
        type t = struct_t reader_t
        let has_stmts x =
          RA_.has_field x 0
        let stmts_get x = 
          RA_.get_struct_list x 0
        let stmts_get_list x =
          Capnp.Array.to_list (stmts_get x)
        let stmts_get_array x =
          Capnp.Array.to_array (stmts_get x)
        let has_r_brace x =
          RA_.has_field x 1
        let r_brace_get x =
          RA_.get_struct x 1
        let r_brace_get_pipelined x =
          MessageWrapper.Untyped.struct_field x 1
        let of_message x = RA_.get_root_struct (RA_.Message.readonly x)
        let of_builder x = Some (RA_.StructStorage.readonly x)
      end
      module While = struct
        type struct_t = [`While_ef7716d0539edb37]
        type t = struct_t reader_t
        let has_cond x =
          RA_.has_field x 0
        let cond_get x =
          RA_.get_struct x 0
        let cond_get_pipelined x =
          MessageWrapper.Untyped.struct_field x 0
        let has_body x =
          RA_.has_field x 1
        let body_get x =
          RA_.get_struct x 1
        let body_get_pipelined x =
          MessageWrapper.Untyped.struct_field x 1
        let has_spec x =
          RA_.has_field x 2
        let spec_get x = 
          RA_.get_struct_list x 2
        let spec_get_list x =
          Capnp.Array.to_list (spec_get x)
        let spec_get_array x =
          Capnp.Array.to_array (spec_get x)
        let has_while_loc x =
          RA_.has_field x 3
        let while_loc_get x =
          RA_.get_struct x 3
        let while_loc_get_pipelined x =
          MessageWrapper.Untyped.struct_field x 3
        let of_message x = RA_.get_root_struct (RA_.Message.readonly x)
        let of_builder x = Some (RA_.StructStorage.readonly x)
      end
      module Case = struct
        type struct_t = [`Case_d41d9dffe36da558]
        type t = struct_t reader_t
        let has_lhs x =
          RA_.has_field x 0
        let lhs_get x =
          RA_.get_struct x 0
        let lhs_get_pipelined x =
          MessageWrapper.Untyped.struct_field x 0
        let has_stmt x =
          RA_.has_field x 1
        let stmt_get x =
          RA_.get_struct x 1
        let stmt_get_pipelined x =
          MessageWrapper.Untyped.struct_field x 1
        let of_message x = RA_.get_root_struct (RA_.Message.readonly x)
        let of_builder x = Some (RA_.StructStorage.readonly x)
      end
      module DefCase = struct
        type struct_t = [`DefCase_ef0bcc479ff59f3e]
        type t = struct_t reader_t
        let has_stmt x =
          RA_.has_field x 0
        let stmt_get x =
          RA_.get_struct x 0
        let stmt_get_pipelined x =
          MessageWrapper.Untyped.struct_field x 0
        let of_message x = RA_.get_root_struct (RA_.Message.readonly x)
        let of_builder x = Some (RA_.StructStorage.readonly x)
      end
      module Switch = struct
        type struct_t = [`Switch_ffc6828955aafac4]
        type t = struct_t reader_t
        let has_cond x =
          RA_.has_field x 0
        let cond_get x =
          RA_.get_struct x 0
        let cond_get_pipelined x =
          MessageWrapper.Untyped.struct_field x 0
        let has_cases x =
          RA_.has_field x 1
        let cases_get x = 
          RA_.get_struct_list x 1
        let cases_get_list x =
          Capnp.Array.to_list (cases_get x)
        let cases_get_array x =
          Capnp.Array.to_array (cases_get x)
        let of_message x = RA_.get_root_struct (RA_.Message.readonly x)
        let of_builder x = Some (RA_.StructStorage.readonly x)
      end
      let union_not_initialized_get x = ()
      let has_ann x =
        RA_.has_field x 0
      let ann_get x =
        RA_.get_text ~default:"" x 0
      let has_decl x =
        RA_.has_field x 0
      let decl_get x = 
        RA_.get_struct_list x 0
      let decl_get_list x =
        Capnp.Array.to_list (decl_get x)
      let decl_get_array x =
        Capnp.Array.to_array (decl_get x)
      let has_compound x =
        RA_.has_field x 0
      let compound_get x =
        RA_.get_struct x 0
      let compound_get_pipelined x =
        MessageWrapper.Untyped.struct_field x 0
      let has_expr x =
        RA_.has_field x 0
      let expr_get x =
        RA_.get_struct x 0
      let expr_get_pipelined x =
        MessageWrapper.Untyped.struct_field x 0
      let has_return x =
        RA_.has_field x 0
      let return_get x =
        RA_.get_struct x 0
      let return_get_pipelined x =
        MessageWrapper.Untyped.struct_field x 0
      let has_if x =
        RA_.has_field x 0
      let if_get x =
        RA_.get_struct x 0
      let if_get_pipelined x =
        MessageWrapper.Untyped.struct_field x 0
      let null_get x = ()
      let has_while x =
        RA_.has_field x 0
      let while_get x =
        RA_.get_struct x 0
      let while_get_pipelined x =
        MessageWrapper.Untyped.struct_field x 0
      let has_do_while x =
        RA_.has_field x 0
      let do_while_get x =
        RA_.get_struct x 0
      let do_while_get_pipelined x =
        MessageWrapper.Untyped.struct_field x 0
      let break_get x = ()
      let continue_get x = ()
      let has_switch x =
        RA_.has_field x 0
      let switch_get x =
        RA_.get_struct x 0
      let switch_get_pipelined x =
        MessageWrapper.Untyped.struct_field x 0
      let has_case x =
        RA_.has_field x 0
      let case_get x =
        RA_.get_struct x 0
      let case_get_pipelined x =
        MessageWrapper.Untyped.struct_field x 0
      let has_def_case x =
        RA_.has_field x 0
      let def_case_get x =
        RA_.get_struct x 0
      let def_case_get_pipelined x =
        MessageWrapper.Untyped.struct_field x 0
      type unnamed_union_t =
        | UnionNotInitialized
        | Ann of string
        | Decl of (ro, Node.t, array_t) Capnp.Array.t
        | Compound of [`Compound_899b868295a7b9ce] reader_t
        | Expr of Node.t
        | Return of [`Return_fe7af58e3af28b84] reader_t
        | If of [`If_bfef959001088175] reader_t
        | Null
        | While of [`While_ef7716d0539edb37] reader_t
        | DoWhile of [`While_ef7716d0539edb37] reader_t
        | Break
        | Continue
        | Switch of [`Switch_ffc6828955aafac4] reader_t
        | Case of [`Case_d41d9dffe36da558] reader_t
        | DefCase of [`DefCase_ef0bcc479ff59f3e] reader_t
        | Undefined of int
      let get x =
        match RA_.get_uint16 ~default:0 x 0 with
        | 0 -> UnionNotInitialized
        | 1 -> Ann (ann_get x)
        | 2 -> Decl (decl_get x)
        | 3 -> Compound (compound_get x)
        | 4 -> Expr (expr_get x)
        | 5 -> Return (return_get x)
        | 6 -> If (if_get x)
        | 7 -> Null
        | 8 -> While (while_get x)
        | 9 -> DoWhile (do_while_get x)
        | 10 -> Break
        | 11 -> Continue
        | 12 -> Switch (switch_get x)
        | 13 -> Case (case_get x)
        | 14 -> DefCase (def_case_get x)
        | v -> Undefined v
      let of_message x = RA_.get_root_struct (RA_.Message.readonly x)
      let of_builder x = Some (RA_.StructStorage.readonly x)
    end
    module Clause = struct
      type struct_t = [`Clause_adb9aafdab430c1d]
      type t = struct_t reader_t
      let has_loc x =
        RA_.has_field x 0
      let loc_get x =
        RA_.get_struct x 0
      let loc_get_pipelined x =
        MessageWrapper.Untyped.struct_field x 0
      let has_text x =
        RA_.has_field x 1
      let text_get x =
        RA_.get_text ~default:"" x 1
      let of_message x = RA_.get_root_struct (RA_.Message.readonly x)
      let of_builder x = Some (RA_.StructStorage.readonly x)
    end
    module RecordKind = struct
      type t = RecordKind_12907431634679073908.t =
        | Struc
        | Class
        | Unio
        | Undefined of int
    end
    module Decl = struct
      type struct_t = [`Decl_d96c7f8624e22938]
      type t = struct_t reader_t
      module Param = struct
        type struct_t = [`Param_97bce41c55c2994a]
        type t = struct_t reader_t
        let has_type x =
          RA_.has_field x 0
        let type_get x =
          RA_.get_struct x 0
        let type_get_pipelined x =
          MessageWrapper.Untyped.struct_field x 0
        let has_name x =
          RA_.has_field x 1
        let name_get x =
          RA_.get_text ~default:"" x 1
        let has_default x =
          RA_.has_field x 2
        let default_get x =
          RA_.get_struct x 2
        let default_get_pipelined x =
          MessageWrapper.Untyped.struct_field x 2
        let of_message x = RA_.get_root_struct (RA_.Message.readonly x)
        let of_builder x = Some (RA_.StructStorage.readonly x)
      end
      module Var = struct
        type struct_t = [`Var_8da2907bb130c41c]
        type t = struct_t reader_t
        module InitStyle = struct
          type t = InitStyle_15285372864656172726.t =
            | CInit
            | CallInit
            | ListInit
            | Undefined of int
        end
        module VarInit = struct
          type struct_t = [`VarInit_96ff0430cb165092]
          type t = struct_t reader_t
          let has_init x =
            RA_.has_field x 0
          let init_get x =
            RA_.get_struct x 0
          let init_get_pipelined x =
            MessageWrapper.Untyped.struct_field x 0
          let style_get x =
            let discr = RA_.get_uint16 ~default:0 x 0 in
            InitStyle_15285372864656172726.decode discr
          let of_message x = RA_.get_root_struct (RA_.Message.readonly x)
          let of_builder x = Some (RA_.StructStorage.readonly x)
        end
        let has_name x =
          RA_.has_field x 0
        let name_get x =
          RA_.get_text ~default:"" x 0
        let has_type x =
          RA_.has_field x 1
        let type_get x =
          RA_.get_struct x 1
        let type_get_pipelined x =
          MessageWrapper.Untyped.struct_field x 1
        let has_init x =
          RA_.has_field x 2
        let init_get x =
          RA_.get_struct x 2
        let init_get_pipelined x =
          MessageWrapper.Untyped.struct_field x 2
        let of_message x = RA_.get_root_struct (RA_.Message.readonly x)
        let of_builder x = Some (RA_.StructStorage.readonly x)
      end
      module Function = struct
        type struct_t = [`Function_d64c65470b140c81]
        type t = struct_t reader_t
        let has_name x =
          RA_.has_field x 0
        let name_get x =
          RA_.get_text ~default:"" x 0
        let has_body x =
          RA_.has_field x 1
        let body_get x =
          RA_.get_struct x 1
        let body_get_pipelined x =
          MessageWrapper.Untyped.struct_field x 1
        let has_result x =
          RA_.has_field x 2
        let result_get x =
          RA_.get_struct x 2
        let result_get_pipelined x =
          MessageWrapper.Untyped.struct_field x 2
        let has_params x =
          RA_.has_field x 3
        let params_get x = 
          RA_.get_struct_list x 3
        let params_get_list x =
          Capnp.Array.to_list (params_get x)
        let params_get_array x =
          Capnp.Array.to_array (params_get x)
        let has_contract x =
          RA_.has_field x 4
        let contract_get x = 
          RA_.get_struct_list x 4
        let contract_get_list x =
          Capnp.Array.to_list (contract_get x)
        let contract_get_array x =
          Capnp.Array.to_array (contract_get x)
        let of_message x = RA_.get_root_struct (RA_.Message.readonly x)
        let of_builder x = Some (RA_.StructStorage.readonly x)
      end
      module Field = struct
        type struct_t = [`Field_ca43d1968400194b]
        type t = struct_t reader_t
        module InitStyle = struct
          type t = InitStyle_13739150215916644662.t =
            | CopyInit
            | ListInit
            | Undefined of int
        end
        module FieldInit = struct
          type struct_t = [`FieldInit_91afac6d2dc82432]
          type t = struct_t reader_t
          let has_init x =
            RA_.has_field x 0
          let init_get x =
            RA_.get_struct x 0
          let init_get_pipelined x =
            MessageWrapper.Untyped.struct_field x 0
          let style_get x =
            let discr = RA_.get_uint16 ~default:0 x 0 in
            InitStyle_13739150215916644662.decode discr
          let of_message x = RA_.get_root_struct (RA_.Message.readonly x)
          let of_builder x = Some (RA_.StructStorage.readonly x)
        end
        let has_name x =
          RA_.has_field x 0
        let name_get x =
          RA_.get_text ~default:"" x 0
        let has_type x =
          RA_.has_field x 1
        let type_get x =
          RA_.get_struct x 1
        let type_get_pipelined x =
          MessageWrapper.Untyped.struct_field x 1
        let has_init x =
          RA_.has_field x 2
        let init_get x =
          RA_.get_struct x 2
        let init_get_pipelined x =
          MessageWrapper.Untyped.struct_field x 2
        let of_message x = RA_.get_root_struct (RA_.Message.readonly x)
        let of_builder x = Some (RA_.StructStorage.readonly x)
      end
      module Record = struct
        type struct_t = [`Record_c925b09644ce72d3]
        type t = struct_t reader_t
        let has_name x =
          RA_.has_field x 0
        let name_get x =
          RA_.get_text ~default:"" x 0
        let kind_get x =
          let discr = RA_.get_uint16 ~default:0 x 0 in
          RecordKind_12907431634679073908.decode discr
        let has_fields x =
          RA_.has_field x 1
        let fields_get x = 
          RA_.get_struct_list x 1
        let fields_get_list x =
          Capnp.Array.to_list (fields_get x)
        let fields_get_array x =
          Capnp.Array.to_array (fields_get x)
        let has_methods x =
          RA_.has_field x 2
        let methods_get x = 
          RA_.get_struct_list x 2
        let methods_get_list x =
          Capnp.Array.to_list (methods_get x)
        let methods_get_array x =
          Capnp.Array.to_array (methods_get x)
        let has_def_get x =
          RA_.get_bit ~default:false x ~byte_ofs:2 ~bit_ofs:0
        let has_decls x =
          RA_.has_field x 3
        let decls_get x = 
          RA_.get_struct_list x 3
        let decls_get_list x =
          Capnp.Array.to_list (decls_get x)
        let decls_get_array x =
          Capnp.Array.to_array (decls_get x)
        let of_message x = RA_.get_root_struct (RA_.Message.readonly x)
        let of_builder x = Some (RA_.StructStorage.readonly x)
      end
      module Method = struct
        type struct_t = [`Method_bebeef9161eb7d3c]
        type t = struct_t reader_t
        let static_get x =
          RA_.get_bit ~default:false x ~byte_ofs:0 ~bit_ofs:0
        let has_func x =
          RA_.has_field x 0
        let func_get x =
          RA_.get_struct x 0
        let func_get_pipelined x =
          MessageWrapper.Untyped.struct_field x 0
        let has_this x =
          RA_.has_field x 1
        let this_get x =
          RA_.get_struct x 1
        let this_get_pipelined x =
          MessageWrapper.Untyped.struct_field x 1
        let of_message x = RA_.get_root_struct (RA_.Message.readonly x)
        let of_builder x = Some (RA_.StructStorage.readonly x)
      end
      module Typedef = struct
        type struct_t = [`Typedef_e46ae190d3365bca]
        type t = struct_t reader_t
        let has_type x =
          RA_.has_field x 0
        let type_get x =
          RA_.get_struct x 0
        let type_get_pipelined x =
          MessageWrapper.Untyped.struct_field x 0
        let has_name x =
          RA_.has_field x 1
        let name_get x =
          RA_.get_text ~default:"" x 1
        let of_message x = RA_.get_root_struct (RA_.Message.readonly x)
        let of_builder x = Some (RA_.StructStorage.readonly x)
      end
      module Enum = struct
        type struct_t = [`Enum_daecdb4dcd868ea8]
        type t = struct_t reader_t
        module EnumField = struct
          type struct_t = [`EnumField_87676bdbadd4545d]
          type t = struct_t reader_t
          let has_name x =
            RA_.has_field x 0
          let name_get x =
            RA_.get_text ~default:"" x 0
          let has_expr x =
            RA_.has_field x 1
          let expr_get x =
            RA_.get_struct x 1
          let expr_get_pipelined x =
            MessageWrapper.Untyped.struct_field x 1
          let of_message x = RA_.get_root_struct (RA_.Message.readonly x)
          let of_builder x = Some (RA_.StructStorage.readonly x)
        end
        let has_name x =
          RA_.has_field x 0
        let name_get x =
          RA_.get_text ~default:"" x 0
        let has_fields x =
          RA_.has_field x 1
        let fields_get x = 
          RA_.get_struct_list x 1
        let fields_get_list x =
          Capnp.Array.to_list (fields_get x)
        let fields_get_array x =
          Capnp.Array.to_array (fields_get x)
        let of_message x = RA_.get_root_struct (RA_.Message.readonly x)
        let of_builder x = Some (RA_.StructStorage.readonly x)
      end
      let union_not_initialized_get x = ()
      let has_ann x =
        RA_.has_field x 0
      let ann_get x =
        RA_.get_text ~default:"" x 0
      let empty_get x = ()
      let has_var x =
        RA_.has_field x 0
      let var_get x =
        RA_.get_struct x 0
      let var_get_pipelined x =
        MessageWrapper.Untyped.struct_field x 0
      let has_function x =
        RA_.has_field x 0
      let function_get x =
        RA_.get_struct x 0
      let function_get_pipelined x =
        MessageWrapper.Untyped.struct_field x 0
      let has_field x =
        RA_.has_field x 0
      let field_get x =
        RA_.get_struct x 0
      let field_get_pipelined x =
        MessageWrapper.Untyped.struct_field x 0
      let has_record x =
        RA_.has_field x 0
      let record_get x =
        RA_.get_struct x 0
      let record_get_pipelined x =
        MessageWrapper.Untyped.struct_field x 0
      let has_method x =
        RA_.has_field x 0
      let method_get x =
        RA_.get_struct x 0
      let method_get_pipelined x =
        MessageWrapper.Untyped.struct_field x 0
      let access_spec_get x = ()
      let def_destructor_get x = ()
      let def_constructor_get x = ()
      let has_typedef x =
        RA_.has_field x 0
      let typedef_get x =
        RA_.get_struct x 0
      let typedef_get_pipelined x =
        MessageWrapper.Untyped.struct_field x 0
      let has_enum_decl x =
        RA_.has_field x 0
      let enum_decl_get x =
        RA_.get_struct x 0
      let enum_decl_get_pipelined x =
        MessageWrapper.Untyped.struct_field x 0
      type unnamed_union_t =
        | UnionNotInitialized
        | Ann of string
        | Empty
        | Var of [`Var_8da2907bb130c41c] reader_t
        | Function of [`Function_d64c65470b140c81] reader_t
        | Field of [`Field_ca43d1968400194b] reader_t
        | Record of [`Record_c925b09644ce72d3] reader_t
        | Method of [`Method_bebeef9161eb7d3c] reader_t
        | AccessSpec
        | DefDestructor
        | DefConstructor
        | Typedef of [`Typedef_e46ae190d3365bca] reader_t
        | EnumDecl of [`Enum_daecdb4dcd868ea8] reader_t
        | Undefined of int
      let get x =
        match RA_.get_uint16 ~default:0 x 0 with
        | 0 -> UnionNotInitialized
        | 1 -> Ann (ann_get x)
        | 2 -> Empty
        | 3 -> Var (var_get x)
        | 4 -> Function (function_get x)
        | 5 -> Field (field_get x)
        | 6 -> Record (record_get x)
        | 7 -> Method (method_get x)
        | 8 -> AccessSpec
        | 9 -> DefDestructor
        | 10 -> DefConstructor
        | 11 -> Typedef (typedef_get x)
        | 12 -> EnumDecl (enum_decl_get x)
        | v -> Undefined v
      let of_message x = RA_.get_root_struct (RA_.Message.readonly x)
      let of_builder x = Some (RA_.StructStorage.readonly x)
    end
    module UnaryOpKind = struct
      type t = UnaryOpKind_16270584510146119878.t =
        | Plus
        | Minus
        | Not
        | LNot
        | AddrOf
        | Deref
        | PreInc
        | PreDec
        | PostInc
        | PostDec
        | Undefined of int
    end
    module BinaryOpKind = struct
      type t = BinaryOpKind_15775553773985184773.t =
        | Add
        | Sub
        | Assign
        | Mul
        | Div
        | Rem
        | Shl
        | Shr
        | Lt
        | Gt
        | Le
        | Ge
        | Eq
        | Ne
        | And
        | Or
        | Xor
        | LAnd
        | LOr
        | MulAssign
        | DivAssign
        | RemAssign
        | AddAssign
        | SubAssign
        | ShlAssign
        | ShrAssign
        | AndAssign
        | XorAssign
        | OrAssign
        | Undefined of int
    end
    module SufKind = struct
      type t = SufKind_10349718269051794478.t =
        | LSuf
        | LLSuf
        | NoSuf
        | Undefined of int
    end
    module NbBase = struct
      type t = NbBase_15750048951651279863.t =
        | Decimal
        | Octal
        | Hex
        | Undefined of int
    end
    module Expr = struct
      type struct_t = [`Expr_d5d009cc85c86562]
      type t = struct_t reader_t
      module UnaryOp = struct
        type struct_t = [`UnaryOp_b525d86a8f48e679]
        type t = struct_t reader_t
        let has_operand x =
          RA_.has_field x 0
        let operand_get x =
          RA_.get_struct x 0
        let operand_get_pipelined x =
          MessageWrapper.Untyped.struct_field x 0
        let kind_get x =
          let discr = RA_.get_uint16 ~default:0 x 0 in
          UnaryOpKind_16270584510146119878.decode discr
        let of_message x = RA_.get_root_struct (RA_.Message.readonly x)
        let of_builder x = Some (RA_.StructStorage.readonly x)
      end
      module BinaryOp = struct
        type struct_t = [`BinaryOp_b95e9a5df08d277c]
        type t = struct_t reader_t
        let has_lhs x =
          RA_.has_field x 0
        let lhs_get x =
          RA_.get_struct x 0
        let lhs_get_pipelined x =
          MessageWrapper.Untyped.struct_field x 0
        let has_rhs x =
          RA_.has_field x 1
        let rhs_get x =
          RA_.get_struct x 1
        let rhs_get_pipelined x =
          MessageWrapper.Untyped.struct_field x 1
        let kind_get x =
          let discr = RA_.get_uint16 ~default:0 x 0 in
          BinaryOpKind_15775553773985184773.decode discr
        let of_message x = RA_.get_root_struct (RA_.Message.readonly x)
        let of_builder x = Some (RA_.StructStorage.readonly x)
      end
      module IntLit = struct
        type struct_t = [`IntLit_a21731ff472a9631]
        type t = struct_t reader_t
        let has_value x =
          RA_.has_field x 0
        let value_get x =
          RA_.get_text ~default:"" x 0
        let u_suffix_get x =
          RA_.get_bit ~default:false x ~byte_ofs:0 ~bit_ofs:0
        let l_suffix_get x =
          let discr = RA_.get_uint16 ~default:0 x 2 in
          SufKind_10349718269051794478.decode discr
        let base_get x =
          let discr = RA_.get_uint16 ~default:0 x 4 in
          NbBase_15750048951651279863.decode discr
        let of_message x = RA_.get_root_struct (RA_.Message.readonly x)
        let of_builder x = Some (RA_.StructStorage.readonly x)
      end
      module Call = struct
        type struct_t = [`Call_d6c567dfeede9b58]
        type t = struct_t reader_t
        let has_args x =
          RA_.has_field x 0
        let args_get x = 
          RA_.get_struct_list x 0
        let args_get_list x =
          Capnp.Array.to_list (args_get x)
        let args_get_array x =
          Capnp.Array.to_array (args_get x)
        let has_callee x =
          RA_.has_field x 1
        let callee_get x =
          RA_.get_struct x 1
        let callee_get_pipelined x =
          MessageWrapper.Untyped.struct_field x 1
        let of_message x = RA_.get_root_struct (RA_.Message.readonly x)
        let of_builder x = Some (RA_.StructStorage.readonly x)
      end
      module Member = struct
        type struct_t = [`Member_ab509764d68e7721]
        type t = struct_t reader_t
        let has_base x =
          RA_.has_field x 0
        let base_get x =
          RA_.get_struct x 0
        let base_get_pipelined x =
          MessageWrapper.Untyped.struct_field x 0
        let has_name x =
          RA_.has_field x 1
        let name_get x =
          RA_.get_text ~default:"" x 1
        let arrow_get x =
          RA_.get_bit ~default:false x ~byte_ofs:0 ~bit_ofs:0
        let of_message x = RA_.get_root_struct (RA_.Message.readonly x)
        let of_builder x = Some (RA_.StructStorage.readonly x)
      end
      module New = struct
        type struct_t = [`New_e0dbc3751d359960]
        type t = struct_t reader_t
        let has_type x =
          RA_.has_field x 0
        let type_get x =
          RA_.get_struct x 0
        let type_get_pipelined x =
          MessageWrapper.Untyped.struct_field x 0
        let has_expr x =
          RA_.has_field x 1
        let expr_get x =
          RA_.get_struct x 1
        let expr_get_pipelined x =
          MessageWrapper.Untyped.struct_field x 1
        let of_message x = RA_.get_root_struct (RA_.Message.readonly x)
        let of_builder x = Some (RA_.StructStorage.readonly x)
      end
      let union_not_initialized_get x = ()
      let has_unary_op x =
        RA_.has_field x 0
      let unary_op_get x =
        RA_.get_struct x 0
      let unary_op_get_pipelined x =
        MessageWrapper.Untyped.struct_field x 0
      let has_binary_op x =
        RA_.has_field x 0
      let binary_op_get x =
        RA_.get_struct x 0
      let binary_op_get_pipelined x =
        MessageWrapper.Untyped.struct_field x 0
      let bool_lit_get x =
        RA_.get_bit ~default:false x ~byte_ofs:2 ~bit_ofs:0
      let has_int_lit x =
        RA_.has_field x 0
      let int_lit_get x =
        RA_.get_struct x 0
      let int_lit_get_pipelined x =
        MessageWrapper.Untyped.struct_field x 0
      let has_string_lit x =
        RA_.has_field x 0
      let string_lit_get x =
        RA_.get_text ~default:"" x 0
      let has_call x =
        RA_.has_field x 0
      let call_get x =
        RA_.get_struct x 0
      let call_get_pipelined x =
        MessageWrapper.Untyped.struct_field x 0
      let has_decl_ref x =
        RA_.has_field x 0
      let decl_ref_get x =
        RA_.get_text ~default:"" x 0
      let has_member x =
        RA_.has_field x 0
      let member_get x =
        RA_.get_struct x 0
      let member_get_pipelined x =
        MessageWrapper.Untyped.struct_field x 0
      let this_get x = ()
      let has_member_call x =
        RA_.has_field x 0
      let member_call_get x =
        RA_.get_struct x 0
      let member_call_get_pipelined x =
        MessageWrapper.Untyped.struct_field x 0
      let has_new x =
        RA_.has_field x 0
      let new_get x =
        RA_.get_struct x 0
      let new_get_pipelined x =
        MessageWrapper.Untyped.struct_field x 0
      let has_construct x =
        RA_.has_field x 0
      let construct_get x = 
        RA_.get_struct_list x 0
      let construct_get_list x =
        Capnp.Array.to_list (construct_get x)
      let construct_get_array x =
        Capnp.Array.to_array (construct_get x)
      let null_ptr_lit_get x = ()
      type unnamed_union_t =
        | UnionNotInitialized
        | UnaryOp of [`UnaryOp_b525d86a8f48e679] reader_t
        | BinaryOp of [`BinaryOp_b95e9a5df08d277c] reader_t
        | BoolLit of bool
        | IntLit of [`IntLit_a21731ff472a9631] reader_t
        | StringLit of string
        | Call of [`Call_d6c567dfeede9b58] reader_t
        | DeclRef of string
        | Member of [`Member_ab509764d68e7721] reader_t
        | This
        | MemberCall of [`Call_d6c567dfeede9b58] reader_t
        | New of [`New_e0dbc3751d359960] reader_t
        | Construct of (ro, Node.t, array_t) Capnp.Array.t
        | NullPtrLit
        | Undefined of int
      let get x =
        match RA_.get_uint16 ~default:0 x 0 with
        | 0 -> UnionNotInitialized
        | 1 -> UnaryOp (unary_op_get x)
        | 2 -> BinaryOp (binary_op_get x)
        | 3 -> BoolLit (bool_lit_get x)
        | 4 -> IntLit (int_lit_get x)
        | 5 -> StringLit (string_lit_get x)
        | 6 -> Call (call_get x)
        | 7 -> DeclRef (decl_ref_get x)
        | 8 -> Member (member_get x)
        | 9 -> This
        | 10 -> MemberCall (member_call_get x)
        | 11 -> New (new_get x)
        | 12 -> Construct (construct_get x)
        | 13 -> NullPtrLit
        | v -> Undefined v
      let of_message x = RA_.get_root_struct (RA_.Message.readonly x)
      let of_builder x = Some (RA_.StructStorage.readonly x)
    end
    module TU = struct
      type struct_t = [`TU_c63033d95787d2ff]
      type t = struct_t reader_t
      module FileEntry = struct
        type struct_t = [`FileEntry_8f25ab49a7ca891f]
        type t = struct_t reader_t
        let fd_get x =
          RA_.get_uint16 ~default:0 x 0
        let has_name x =
          RA_.has_field x 0
        let name_get x =
          RA_.get_text ~default:"" x 0
        let of_message x = RA_.get_root_struct (RA_.Message.readonly x)
        let of_builder x = Some (RA_.StructStorage.readonly x)
      end
      let has_decls x =
        RA_.has_field x 0
      let decls_get x = 
        RA_.get_struct_list x 0
      let decls_get_list x =
        Capnp.Array.to_list (decls_get x)
      let decls_get_array x =
        Capnp.Array.to_array (decls_get x)
      let has_files x =
        RA_.has_field x 1
      let files_get x = 
        RA_.get_struct_list x 1
      let files_get_list x =
        Capnp.Array.to_list (files_get x)
      let files_get_array x =
        Capnp.Array.to_array (files_get x)
      let of_message x = RA_.get_root_struct (RA_.Message.readonly x)
      let of_builder x = Some (RA_.StructStorage.readonly x)
    end
    module Err = struct
      type struct_t = [`Err_9162b284a3cba818]
      type t = struct_t reader_t
      let has_loc x =
        RA_.has_field x 0
      let loc_get x =
        RA_.get_struct x 0
      let loc_get_pipelined x =
        MessageWrapper.Untyped.struct_field x 0
      let has_reason x =
        RA_.has_field x 1
      let reason_get x =
        RA_.get_text ~default:"" x 1
      let of_message x = RA_.get_root_struct (RA_.Message.readonly x)
      let of_builder x = Some (RA_.StructStorage.readonly x)
    end
    module SerResult = struct
      type struct_t = [`SerResult_a5cc2b3709c2654d]
      type t = struct_t reader_t
      let ok_get x = ()
      let err_get x = ()
      type unnamed_union_t =
        | Ok
        | Err
        | Undefined of int
      let get x =
        match RA_.get_uint16 ~default:0 x 0 with
        | 0 -> Ok
        | 1 -> Err
        | v -> Undefined v
      let of_message x = RA_.get_root_struct (RA_.Message.readonly x)
      let of_builder x = Some (RA_.StructStorage.readonly x)
    end
  end

  module Builder = struct
    type array_t = Reader.builder_array_t
    type reader_array_t = Reader.array_t
    type pointer_t = rw MessageWrapper.Slice.t

    module Loc = struct
      type struct_t = [`Loc_b1436df23fb200b4]
      type t = struct_t builder_t
      module SrcPos = struct
        type struct_t = [`SrcPos_80bc3ef5a3c049a0]
        type t = struct_t builder_t
        let l_get x =
          BA_.get_uint16 ~default:0 x 0
        let l_set_exn x v =
          BA_.set_uint16 ~default:0 x 0 v
        let c_get x =
          BA_.get_uint16 ~default:0 x 2
        let c_set_exn x v =
          BA_.set_uint16 ~default:0 x 2 v
        let fd_get x =
          BA_.get_uint16 ~default:0 x 4
        let fd_set_exn x v =
          BA_.set_uint16 ~default:0 x 4 v
        let of_message x = BA_.get_root_struct ~data_words:1 ~pointer_words:0 x
        let to_message x = x.BA_.NM.StructStorage.data.MessageWrapper.Slice.msg
        let to_reader x = Some (RA_.StructStorage.readonly x)
        let init_root ?message_size () =
          BA_.alloc_root_struct ?message_size ~data_words:1 ~pointer_words:0 ()
        let init_pointer ptr =
          BA_.init_struct_pointer ptr ~data_words:1 ~pointer_words:0
      end
      let has_start x =
        BA_.has_field x 0
      let start_get x =
        BA_.get_struct ~data_words:1 ~pointer_words:0 x 0
      let start_set_reader x v =
        BA_.set_struct ~data_words:1 ~pointer_words:0 x 0 v
      let start_set_builder x v =
        BA_.set_struct ~data_words:1 ~pointer_words:0 x 0 (Some v)
      let start_init x =
        BA_.init_struct ~data_words:1 ~pointer_words:0 x 0
      let has_end x =
        BA_.has_field x 1
      let end_get x =
        BA_.get_struct ~data_words:1 ~pointer_words:0 x 1
      let end_set_reader x v =
        BA_.set_struct ~data_words:1 ~pointer_words:0 x 1 v
      let end_set_builder x v =
        BA_.set_struct ~data_words:1 ~pointer_words:0 x 1 (Some v)
      let end_init x =
        BA_.init_struct ~data_words:1 ~pointer_words:0 x 1
      let of_message x = BA_.get_root_struct ~data_words:0 ~pointer_words:2 x
      let to_message x = x.BA_.NM.StructStorage.data.MessageWrapper.Slice.msg
      let to_reader x = Some (RA_.StructStorage.readonly x)
      let init_root ?message_size () =
        BA_.alloc_root_struct ?message_size ~data_words:0 ~pointer_words:2 ()
      let init_pointer ptr =
        BA_.init_struct_pointer ptr ~data_words:0 ~pointer_words:2
    end
    module Node = struct
      type struct_t = [`Node_e2a8b78aa50d684a]
      type t = struct_t builder_t
      let has_loc x =
        BA_.has_field x 0
      let loc_get x =
        BA_.get_struct ~data_words:0 ~pointer_words:2 x 0
      let loc_set_reader x v =
        BA_.set_struct ~data_words:0 ~pointer_words:2 x 0 v
      let loc_set_builder x v =
        BA_.set_struct ~data_words:0 ~pointer_words:2 x 0 (Some v)
      let loc_init x =
        BA_.init_struct ~data_words:0 ~pointer_words:2 x 0
      let desc_get x =
        BA_.get_pointer x 1
      let desc_get_interface x =
        BA_.get_interface x 1
      let desc_set x v =
        BA_.set_pointer x 1 (Some v)
      let desc_set_reader x v =
        BA_.set_pointer x 1 v
      let desc_set_interface x v =
        BA_.set_interface x 1 v
      let of_message x = BA_.get_root_struct ~data_words:0 ~pointer_words:2 x
      let to_message x = x.BA_.NM.StructStorage.data.MessageWrapper.Slice.msg
      let to_reader x = Some (RA_.StructStorage.readonly x)
      let init_root ?message_size () =
        BA_.alloc_root_struct ?message_size ~data_words:0 ~pointer_words:2 ()
      let init_pointer ptr =
        BA_.init_struct_pointer ptr ~data_words:0 ~pointer_words:2
    end
    module Type = struct
      type struct_t = [`Type_f4d8929c89991d82]
      type t = struct_t builder_t
      module BuiltinKind = struct
        type t = BuiltinKind_11913544707969661485.t =
          | Char
          | UChar
          | Short
          | UShort
          | Void
          | Bool
          | Int
          | UInt
          | Long
          | ULong
          | LongLong
          | ULongLong
          | Undefined of int
      end
      module Record = struct
        type struct_t = [`Record_f92013bb699d0281]
        type t = struct_t builder_t
        let kind_get x =
          let discr = BA_.get_uint16 ~default:0 x 0 in
          RecordKind_12907431634679073908.decode discr
        let kind_set x e =
          BA_.set_uint16 ~default:0 x 0 (RecordKind_12907431634679073908.encode_safe e)
        let kind_set_unsafe x e =
          BA_.set_uint16 ~default:0 x 0 (RecordKind_12907431634679073908.encode_unsafe e)
        let has_name x =
          BA_.has_field x 0
        let name_get x =
          BA_.get_text ~default:"" x 0
        let name_set x v =
          BA_.set_text x 0 v
        let of_message x = BA_.get_root_struct ~data_words:1 ~pointer_words:1 x
        let to_message x = x.BA_.NM.StructStorage.data.MessageWrapper.Slice.msg
        let to_reader x = Some (RA_.StructStorage.readonly x)
        let init_root ?message_size () =
          BA_.alloc_root_struct ?message_size ~data_words:1 ~pointer_words:1 ()
        let init_pointer ptr =
          BA_.init_struct_pointer ptr ~data_words:1 ~pointer_words:1
      end
      let builtin_get x =
        let discr = BA_.get_uint16 ~default:0 x 0 in
        BuiltinKind_11913544707969661485.decode discr
      let builtin_set x e =
        BA_.set_uint16 ~discr:{BA_.Discr.value=0; BA_.Discr.byte_ofs=2} ~default:0 x 0 (BuiltinKind_11913544707969661485.encode_safe e)
      let builtin_set_unsafe x e =
        BA_.set_uint16 ~discr:{BA_.Discr.value=0; BA_.Discr.byte_ofs=2} ~default:0 x 0 (BuiltinKind_11913544707969661485.encode_unsafe e)
      let has_pointer x =
        BA_.has_field x 0
      let pointer_get x =
        BA_.get_struct ~data_words:1 ~pointer_words:1 x 0
      let pointer_set_reader x v =
        BA_.set_struct ~data_words:1 ~pointer_words:1 ~discr:{BA_.Discr.value=1; BA_.Discr.byte_ofs=2} x 0 v
      let pointer_set_builder x v =
        BA_.set_struct ~data_words:1 ~pointer_words:1 ~discr:{BA_.Discr.value=1; BA_.Discr.byte_ofs=2} x 0 (Some v)
      let pointer_init x =
        BA_.init_struct ~data_words:1 ~pointer_words:1 ~discr:{BA_.Discr.value=1; BA_.Discr.byte_ofs=2} x 0
      let has_pointer_loc x =
        BA_.has_field x 0
      let pointer_loc_get x =
        BA_.get_struct ~data_words:0 ~pointer_words:2 x 0
      let pointer_loc_set_reader x v =
        BA_.set_struct ~data_words:0 ~pointer_words:2 ~discr:{BA_.Discr.value=2; BA_.Discr.byte_ofs=2} x 0 v
      let pointer_loc_set_builder x v =
        BA_.set_struct ~data_words:0 ~pointer_words:2 ~discr:{BA_.Discr.value=2; BA_.Discr.byte_ofs=2} x 0 (Some v)
      let pointer_loc_init x =
        BA_.init_struct ~data_words:0 ~pointer_words:2 ~discr:{BA_.Discr.value=2; BA_.Discr.byte_ofs=2} x 0
      let has_record x =
        BA_.has_field x 0
      let record_get x =
        BA_.get_struct ~data_words:1 ~pointer_words:1 x 0
      let record_set_reader x v =
        BA_.set_struct ~data_words:1 ~pointer_words:1 ~discr:{BA_.Discr.value=3; BA_.Discr.byte_ofs=2} x 0 v
      let record_set_builder x v =
        BA_.set_struct ~data_words:1 ~pointer_words:1 ~discr:{BA_.Discr.value=3; BA_.Discr.byte_ofs=2} x 0 (Some v)
      let record_init x =
        BA_.init_struct ~data_words:1 ~pointer_words:1 ~discr:{BA_.Discr.value=3; BA_.Discr.byte_ofs=2} x 0
      let has_enum_type x =
        BA_.has_field x 0
      let enum_type_get x =
        BA_.get_text ~default:"" x 0
      let enum_type_set x v =
        BA_.set_text ~discr:{BA_.Discr.value=4; BA_.Discr.byte_ofs=2} x 0 v
      type unnamed_union_t =
        | Builtin of BuiltinKind_11913544707969661485.t
        | Pointer of [`Type_f4d8929c89991d82] builder_t
        | PointerLoc of Node.t
        | Record of [`Record_f92013bb699d0281] builder_t
        | EnumType of string
        | Undefined of int
      let get x =
        match BA_.get_uint16 ~default:0 x 2 with
        | 0 -> Builtin (builtin_get x)
        | 1 -> Pointer (pointer_get x)
        | 2 -> PointerLoc (pointer_loc_get x)
        | 3 -> Record (record_get x)
        | 4 -> EnumType (enum_type_get x)
        | v -> Undefined v
      let of_message x = BA_.get_root_struct ~data_words:1 ~pointer_words:1 x
      let to_message x = x.BA_.NM.StructStorage.data.MessageWrapper.Slice.msg
      let to_reader x = Some (RA_.StructStorage.readonly x)
      let init_root ?message_size () =
        BA_.alloc_root_struct ?message_size ~data_words:1 ~pointer_words:1 ()
      let init_pointer ptr =
        BA_.init_struct_pointer ptr ~data_words:1 ~pointer_words:1
    end
    module Stmt = struct
      type struct_t = [`Stmt_f6a0f771ad50816c]
      type t = struct_t builder_t
      module Return = struct
        type struct_t = [`Return_fe7af58e3af28b84]
        type t = struct_t builder_t
        let has_expr x =
          BA_.has_field x 0
        let expr_get x =
          BA_.get_struct ~data_words:0 ~pointer_words:2 x 0
        let expr_set_reader x v =
          BA_.set_struct ~data_words:0 ~pointer_words:2 x 0 v
        let expr_set_builder x v =
          BA_.set_struct ~data_words:0 ~pointer_words:2 x 0 (Some v)
        let expr_init x =
          BA_.init_struct ~data_words:0 ~pointer_words:2 x 0
        let of_message x = BA_.get_root_struct ~data_words:0 ~pointer_words:1 x
        let to_message x = x.BA_.NM.StructStorage.data.MessageWrapper.Slice.msg
        let to_reader x = Some (RA_.StructStorage.readonly x)
        let init_root ?message_size () =
          BA_.alloc_root_struct ?message_size ~data_words:0 ~pointer_words:1 ()
        let init_pointer ptr =
          BA_.init_struct_pointer ptr ~data_words:0 ~pointer_words:1
      end
      module If = struct
        type struct_t = [`If_bfef959001088175]
        type t = struct_t builder_t
        let has_cond x =
          BA_.has_field x 0
        let cond_get x =
          BA_.get_struct ~data_words:0 ~pointer_words:2 x 0
        let cond_set_reader x v =
          BA_.set_struct ~data_words:0 ~pointer_words:2 x 0 v
        let cond_set_builder x v =
          BA_.set_struct ~data_words:0 ~pointer_words:2 x 0 (Some v)
        let cond_init x =
          BA_.init_struct ~data_words:0 ~pointer_words:2 x 0
        let has_then x =
          BA_.has_field x 1
        let then_get x =
          BA_.get_struct ~data_words:0 ~pointer_words:2 x 1
        let then_set_reader x v =
          BA_.set_struct ~data_words:0 ~pointer_words:2 x 1 v
        let then_set_builder x v =
          BA_.set_struct ~data_words:0 ~pointer_words:2 x 1 (Some v)
        let then_init x =
          BA_.init_struct ~data_words:0 ~pointer_words:2 x 1
        let has_else x =
          BA_.has_field x 2
        let else_get x =
          BA_.get_struct ~data_words:0 ~pointer_words:2 x 2
        let else_set_reader x v =
          BA_.set_struct ~data_words:0 ~pointer_words:2 x 2 v
        let else_set_builder x v =
          BA_.set_struct ~data_words:0 ~pointer_words:2 x 2 (Some v)
        let else_init x =
          BA_.init_struct ~data_words:0 ~pointer_words:2 x 2
        let of_message x = BA_.get_root_struct ~data_words:0 ~pointer_words:3 x
        let to_message x = x.BA_.NM.StructStorage.data.MessageWrapper.Slice.msg
        let to_reader x = Some (RA_.StructStorage.readonly x)
        let init_root ?message_size () =
          BA_.alloc_root_struct ?message_size ~data_words:0 ~pointer_words:3 ()
        let init_pointer ptr =
          BA_.init_struct_pointer ptr ~data_words:0 ~pointer_words:3
      end
      module Compound = struct
        type struct_t = [`Compound_899b868295a7b9ce]
        type t = struct_t builder_t
        let has_stmts x =
          BA_.has_field x 0
        let stmts_get x = 
          BA_.get_struct_list ~data_words:0 ~pointer_words:2 x 0
        let stmts_get_list x =
          Capnp.Array.to_list (stmts_get x)
        let stmts_get_array x =
          Capnp.Array.to_array (stmts_get x)
        let stmts_set x v =
          BA_.set_struct_list ~data_words:0 ~pointer_words:2 x 0 v
        let stmts_init x n =
          BA_.init_struct_list ~data_words:0 ~pointer_words:2 x 0 n
        let stmts_set_list x v =
          let builder = stmts_init x (List.length v) in
          let () = List.iteri (fun i a -> Capnp.Array.set builder i a) v in
          builder
        let stmts_set_array x v =
          let builder = stmts_init x (Array.length v) in
          let () = Array.iteri (fun i a -> Capnp.Array.set builder i a) v in
          builder
        let has_r_brace x =
          BA_.has_field x 1
        let r_brace_get x =
          BA_.get_struct ~data_words:0 ~pointer_words:2 x 1
        let r_brace_set_reader x v =
          BA_.set_struct ~data_words:0 ~pointer_words:2 x 1 v
        let r_brace_set_builder x v =
          BA_.set_struct ~data_words:0 ~pointer_words:2 x 1 (Some v)
        let r_brace_init x =
          BA_.init_struct ~data_words:0 ~pointer_words:2 x 1
        let of_message x = BA_.get_root_struct ~data_words:0 ~pointer_words:2 x
        let to_message x = x.BA_.NM.StructStorage.data.MessageWrapper.Slice.msg
        let to_reader x = Some (RA_.StructStorage.readonly x)
        let init_root ?message_size () =
          BA_.alloc_root_struct ?message_size ~data_words:0 ~pointer_words:2 ()
        let init_pointer ptr =
          BA_.init_struct_pointer ptr ~data_words:0 ~pointer_words:2
      end
      module While = struct
        type struct_t = [`While_ef7716d0539edb37]
        type t = struct_t builder_t
        let has_cond x =
          BA_.has_field x 0
        let cond_get x =
          BA_.get_struct ~data_words:0 ~pointer_words:2 x 0
        let cond_set_reader x v =
          BA_.set_struct ~data_words:0 ~pointer_words:2 x 0 v
        let cond_set_builder x v =
          BA_.set_struct ~data_words:0 ~pointer_words:2 x 0 (Some v)
        let cond_init x =
          BA_.init_struct ~data_words:0 ~pointer_words:2 x 0
        let has_body x =
          BA_.has_field x 1
        let body_get x =
          BA_.get_struct ~data_words:0 ~pointer_words:2 x 1
        let body_set_reader x v =
          BA_.set_struct ~data_words:0 ~pointer_words:2 x 1 v
        let body_set_builder x v =
          BA_.set_struct ~data_words:0 ~pointer_words:2 x 1 (Some v)
        let body_init x =
          BA_.init_struct ~data_words:0 ~pointer_words:2 x 1
        let has_spec x =
          BA_.has_field x 2
        let spec_get x = 
          BA_.get_struct_list ~data_words:0 ~pointer_words:2 x 2
        let spec_get_list x =
          Capnp.Array.to_list (spec_get x)
        let spec_get_array x =
          Capnp.Array.to_array (spec_get x)
        let spec_set x v =
          BA_.set_struct_list ~data_words:0 ~pointer_words:2 x 2 v
        let spec_init x n =
          BA_.init_struct_list ~data_words:0 ~pointer_words:2 x 2 n
        let spec_set_list x v =
          let builder = spec_init x (List.length v) in
          let () = List.iteri (fun i a -> Capnp.Array.set builder i a) v in
          builder
        let spec_set_array x v =
          let builder = spec_init x (Array.length v) in
          let () = Array.iteri (fun i a -> Capnp.Array.set builder i a) v in
          builder
        let has_while_loc x =
          BA_.has_field x 3
        let while_loc_get x =
          BA_.get_struct ~data_words:0 ~pointer_words:2 x 3
        let while_loc_set_reader x v =
          BA_.set_struct ~data_words:0 ~pointer_words:2 x 3 v
        let while_loc_set_builder x v =
          BA_.set_struct ~data_words:0 ~pointer_words:2 x 3 (Some v)
        let while_loc_init x =
          BA_.init_struct ~data_words:0 ~pointer_words:2 x 3
        let of_message x = BA_.get_root_struct ~data_words:0 ~pointer_words:4 x
        let to_message x = x.BA_.NM.StructStorage.data.MessageWrapper.Slice.msg
        let to_reader x = Some (RA_.StructStorage.readonly x)
        let init_root ?message_size () =
          BA_.alloc_root_struct ?message_size ~data_words:0 ~pointer_words:4 ()
        let init_pointer ptr =
          BA_.init_struct_pointer ptr ~data_words:0 ~pointer_words:4
      end
      module Case = struct
        type struct_t = [`Case_d41d9dffe36da558]
        type t = struct_t builder_t
        let has_lhs x =
          BA_.has_field x 0
        let lhs_get x =
          BA_.get_struct ~data_words:0 ~pointer_words:2 x 0
        let lhs_set_reader x v =
          BA_.set_struct ~data_words:0 ~pointer_words:2 x 0 v
        let lhs_set_builder x v =
          BA_.set_struct ~data_words:0 ~pointer_words:2 x 0 (Some v)
        let lhs_init x =
          BA_.init_struct ~data_words:0 ~pointer_words:2 x 0
        let has_stmt x =
          BA_.has_field x 1
        let stmt_get x =
          BA_.get_struct ~data_words:0 ~pointer_words:2 x 1
        let stmt_set_reader x v =
          BA_.set_struct ~data_words:0 ~pointer_words:2 x 1 v
        let stmt_set_builder x v =
          BA_.set_struct ~data_words:0 ~pointer_words:2 x 1 (Some v)
        let stmt_init x =
          BA_.init_struct ~data_words:0 ~pointer_words:2 x 1
        let of_message x = BA_.get_root_struct ~data_words:0 ~pointer_words:2 x
        let to_message x = x.BA_.NM.StructStorage.data.MessageWrapper.Slice.msg
        let to_reader x = Some (RA_.StructStorage.readonly x)
        let init_root ?message_size () =
          BA_.alloc_root_struct ?message_size ~data_words:0 ~pointer_words:2 ()
        let init_pointer ptr =
          BA_.init_struct_pointer ptr ~data_words:0 ~pointer_words:2
      end
      module DefCase = struct
        type struct_t = [`DefCase_ef0bcc479ff59f3e]
        type t = struct_t builder_t
        let has_stmt x =
          BA_.has_field x 0
        let stmt_get x =
          BA_.get_struct ~data_words:0 ~pointer_words:2 x 0
        let stmt_set_reader x v =
          BA_.set_struct ~data_words:0 ~pointer_words:2 x 0 v
        let stmt_set_builder x v =
          BA_.set_struct ~data_words:0 ~pointer_words:2 x 0 (Some v)
        let stmt_init x =
          BA_.init_struct ~data_words:0 ~pointer_words:2 x 0
        let of_message x = BA_.get_root_struct ~data_words:0 ~pointer_words:1 x
        let to_message x = x.BA_.NM.StructStorage.data.MessageWrapper.Slice.msg
        let to_reader x = Some (RA_.StructStorage.readonly x)
        let init_root ?message_size () =
          BA_.alloc_root_struct ?message_size ~data_words:0 ~pointer_words:1 ()
        let init_pointer ptr =
          BA_.init_struct_pointer ptr ~data_words:0 ~pointer_words:1
      end
      module Switch = struct
        type struct_t = [`Switch_ffc6828955aafac4]
        type t = struct_t builder_t
        let has_cond x =
          BA_.has_field x 0
        let cond_get x =
          BA_.get_struct ~data_words:0 ~pointer_words:2 x 0
        let cond_set_reader x v =
          BA_.set_struct ~data_words:0 ~pointer_words:2 x 0 v
        let cond_set_builder x v =
          BA_.set_struct ~data_words:0 ~pointer_words:2 x 0 (Some v)
        let cond_init x =
          BA_.init_struct ~data_words:0 ~pointer_words:2 x 0
        let has_cases x =
          BA_.has_field x 1
        let cases_get x = 
          BA_.get_struct_list ~data_words:0 ~pointer_words:2 x 1
        let cases_get_list x =
          Capnp.Array.to_list (cases_get x)
        let cases_get_array x =
          Capnp.Array.to_array (cases_get x)
        let cases_set x v =
          BA_.set_struct_list ~data_words:0 ~pointer_words:2 x 1 v
        let cases_init x n =
          BA_.init_struct_list ~data_words:0 ~pointer_words:2 x 1 n
        let cases_set_list x v =
          let builder = cases_init x (List.length v) in
          let () = List.iteri (fun i a -> Capnp.Array.set builder i a) v in
          builder
        let cases_set_array x v =
          let builder = cases_init x (Array.length v) in
          let () = Array.iteri (fun i a -> Capnp.Array.set builder i a) v in
          builder
        let of_message x = BA_.get_root_struct ~data_words:0 ~pointer_words:2 x
        let to_message x = x.BA_.NM.StructStorage.data.MessageWrapper.Slice.msg
        let to_reader x = Some (RA_.StructStorage.readonly x)
        let init_root ?message_size () =
          BA_.alloc_root_struct ?message_size ~data_words:0 ~pointer_words:2 ()
        let init_pointer ptr =
          BA_.init_struct_pointer ptr ~data_words:0 ~pointer_words:2
      end
      let union_not_initialized_get x = ()
      let union_not_initialized_set x =
        BA_.set_void ~discr:{BA_.Discr.value=0; BA_.Discr.byte_ofs=0} x
      let has_ann x =
        BA_.has_field x 0
      let ann_get x =
        BA_.get_text ~default:"" x 0
      let ann_set x v =
        BA_.set_text ~discr:{BA_.Discr.value=1; BA_.Discr.byte_ofs=0} x 0 v
      let has_decl x =
        BA_.has_field x 0
      let decl_get x = 
        BA_.get_struct_list ~data_words:0 ~pointer_words:2 x 0
      let decl_get_list x =
        Capnp.Array.to_list (decl_get x)
      let decl_get_array x =
        Capnp.Array.to_array (decl_get x)
      let decl_set x v =
        BA_.set_struct_list ~data_words:0 ~pointer_words:2 ~discr:{BA_.Discr.value=2; BA_.Discr.byte_ofs=0} x 0 v
      let decl_init x n =
        BA_.init_struct_list ~data_words:0 ~pointer_words:2 ~discr:{BA_.Discr.value=2; BA_.Discr.byte_ofs=0} x 0 n
      let decl_set_list x v =
        let builder = decl_init x (List.length v) in
        let () = List.iteri (fun i a -> Capnp.Array.set builder i a) v in
        builder
      let decl_set_array x v =
        let builder = decl_init x (Array.length v) in
        let () = Array.iteri (fun i a -> Capnp.Array.set builder i a) v in
        builder
      let has_compound x =
        BA_.has_field x 0
      let compound_get x =
        BA_.get_struct ~data_words:0 ~pointer_words:2 x 0
      let compound_set_reader x v =
        BA_.set_struct ~data_words:0 ~pointer_words:2 ~discr:{BA_.Discr.value=3; BA_.Discr.byte_ofs=0} x 0 v
      let compound_set_builder x v =
        BA_.set_struct ~data_words:0 ~pointer_words:2 ~discr:{BA_.Discr.value=3; BA_.Discr.byte_ofs=0} x 0 (Some v)
      let compound_init x =
        BA_.init_struct ~data_words:0 ~pointer_words:2 ~discr:{BA_.Discr.value=3; BA_.Discr.byte_ofs=0} x 0
      let has_expr x =
        BA_.has_field x 0
      let expr_get x =
        BA_.get_struct ~data_words:0 ~pointer_words:2 x 0
      let expr_set_reader x v =
        BA_.set_struct ~data_words:0 ~pointer_words:2 ~discr:{BA_.Discr.value=4; BA_.Discr.byte_ofs=0} x 0 v
      let expr_set_builder x v =
        BA_.set_struct ~data_words:0 ~pointer_words:2 ~discr:{BA_.Discr.value=4; BA_.Discr.byte_ofs=0} x 0 (Some v)
      let expr_init x =
        BA_.init_struct ~data_words:0 ~pointer_words:2 ~discr:{BA_.Discr.value=4; BA_.Discr.byte_ofs=0} x 0
      let has_return x =
        BA_.has_field x 0
      let return_get x =
        BA_.get_struct ~data_words:0 ~pointer_words:1 x 0
      let return_set_reader x v =
        BA_.set_struct ~data_words:0 ~pointer_words:1 ~discr:{BA_.Discr.value=5; BA_.Discr.byte_ofs=0} x 0 v
      let return_set_builder x v =
        BA_.set_struct ~data_words:0 ~pointer_words:1 ~discr:{BA_.Discr.value=5; BA_.Discr.byte_ofs=0} x 0 (Some v)
      let return_init x =
        BA_.init_struct ~data_words:0 ~pointer_words:1 ~discr:{BA_.Discr.value=5; BA_.Discr.byte_ofs=0} x 0
      let has_if x =
        BA_.has_field x 0
      let if_get x =
        BA_.get_struct ~data_words:0 ~pointer_words:3 x 0
      let if_set_reader x v =
        BA_.set_struct ~data_words:0 ~pointer_words:3 ~discr:{BA_.Discr.value=6; BA_.Discr.byte_ofs=0} x 0 v
      let if_set_builder x v =
        BA_.set_struct ~data_words:0 ~pointer_words:3 ~discr:{BA_.Discr.value=6; BA_.Discr.byte_ofs=0} x 0 (Some v)
      let if_init x =
        BA_.init_struct ~data_words:0 ~pointer_words:3 ~discr:{BA_.Discr.value=6; BA_.Discr.byte_ofs=0} x 0
      let null_get x = ()
      let null_set x =
        BA_.set_void ~discr:{BA_.Discr.value=7; BA_.Discr.byte_ofs=0} x
      let has_while x =
        BA_.has_field x 0
      let while_get x =
        BA_.get_struct ~data_words:0 ~pointer_words:4 x 0
      let while_set_reader x v =
        BA_.set_struct ~data_words:0 ~pointer_words:4 ~discr:{BA_.Discr.value=8; BA_.Discr.byte_ofs=0} x 0 v
      let while_set_builder x v =
        BA_.set_struct ~data_words:0 ~pointer_words:4 ~discr:{BA_.Discr.value=8; BA_.Discr.byte_ofs=0} x 0 (Some v)
      let while_init x =
        BA_.init_struct ~data_words:0 ~pointer_words:4 ~discr:{BA_.Discr.value=8; BA_.Discr.byte_ofs=0} x 0
      let has_do_while x =
        BA_.has_field x 0
      let do_while_get x =
        BA_.get_struct ~data_words:0 ~pointer_words:4 x 0
      let do_while_set_reader x v =
        BA_.set_struct ~data_words:0 ~pointer_words:4 ~discr:{BA_.Discr.value=9; BA_.Discr.byte_ofs=0} x 0 v
      let do_while_set_builder x v =
        BA_.set_struct ~data_words:0 ~pointer_words:4 ~discr:{BA_.Discr.value=9; BA_.Discr.byte_ofs=0} x 0 (Some v)
      let do_while_init x =
        BA_.init_struct ~data_words:0 ~pointer_words:4 ~discr:{BA_.Discr.value=9; BA_.Discr.byte_ofs=0} x 0
      let break_get x = ()
      let break_set x =
        BA_.set_void ~discr:{BA_.Discr.value=10; BA_.Discr.byte_ofs=0} x
      let continue_get x = ()
      let continue_set x =
        BA_.set_void ~discr:{BA_.Discr.value=11; BA_.Discr.byte_ofs=0} x
      let has_switch x =
        BA_.has_field x 0
      let switch_get x =
        BA_.get_struct ~data_words:0 ~pointer_words:2 x 0
      let switch_set_reader x v =
        BA_.set_struct ~data_words:0 ~pointer_words:2 ~discr:{BA_.Discr.value=12; BA_.Discr.byte_ofs=0} x 0 v
      let switch_set_builder x v =
        BA_.set_struct ~data_words:0 ~pointer_words:2 ~discr:{BA_.Discr.value=12; BA_.Discr.byte_ofs=0} x 0 (Some v)
      let switch_init x =
        BA_.init_struct ~data_words:0 ~pointer_words:2 ~discr:{BA_.Discr.value=12; BA_.Discr.byte_ofs=0} x 0
      let has_case x =
        BA_.has_field x 0
      let case_get x =
        BA_.get_struct ~data_words:0 ~pointer_words:2 x 0
      let case_set_reader x v =
        BA_.set_struct ~data_words:0 ~pointer_words:2 ~discr:{BA_.Discr.value=13; BA_.Discr.byte_ofs=0} x 0 v
      let case_set_builder x v =
        BA_.set_struct ~data_words:0 ~pointer_words:2 ~discr:{BA_.Discr.value=13; BA_.Discr.byte_ofs=0} x 0 (Some v)
      let case_init x =
        BA_.init_struct ~data_words:0 ~pointer_words:2 ~discr:{BA_.Discr.value=13; BA_.Discr.byte_ofs=0} x 0
      let has_def_case x =
        BA_.has_field x 0
      let def_case_get x =
        BA_.get_struct ~data_words:0 ~pointer_words:1 x 0
      let def_case_set_reader x v =
        BA_.set_struct ~data_words:0 ~pointer_words:1 ~discr:{BA_.Discr.value=14; BA_.Discr.byte_ofs=0} x 0 v
      let def_case_set_builder x v =
        BA_.set_struct ~data_words:0 ~pointer_words:1 ~discr:{BA_.Discr.value=14; BA_.Discr.byte_ofs=0} x 0 (Some v)
      let def_case_init x =
        BA_.init_struct ~data_words:0 ~pointer_words:1 ~discr:{BA_.Discr.value=14; BA_.Discr.byte_ofs=0} x 0
      type unnamed_union_t =
        | UnionNotInitialized
        | Ann of string
        | Decl of (rw, Node.t, array_t) Capnp.Array.t
        | Compound of [`Compound_899b868295a7b9ce] builder_t
        | Expr of Node.t
        | Return of [`Return_fe7af58e3af28b84] builder_t
        | If of [`If_bfef959001088175] builder_t
        | Null
        | While of [`While_ef7716d0539edb37] builder_t
        | DoWhile of [`While_ef7716d0539edb37] builder_t
        | Break
        | Continue
        | Switch of [`Switch_ffc6828955aafac4] builder_t
        | Case of [`Case_d41d9dffe36da558] builder_t
        | DefCase of [`DefCase_ef0bcc479ff59f3e] builder_t
        | Undefined of int
      let get x =
        match BA_.get_uint16 ~default:0 x 0 with
        | 0 -> UnionNotInitialized
        | 1 -> Ann (ann_get x)
        | 2 -> Decl (decl_get x)
        | 3 -> Compound (compound_get x)
        | 4 -> Expr (expr_get x)
        | 5 -> Return (return_get x)
        | 6 -> If (if_get x)
        | 7 -> Null
        | 8 -> While (while_get x)
        | 9 -> DoWhile (do_while_get x)
        | 10 -> Break
        | 11 -> Continue
        | 12 -> Switch (switch_get x)
        | 13 -> Case (case_get x)
        | 14 -> DefCase (def_case_get x)
        | v -> Undefined v
      let of_message x = BA_.get_root_struct ~data_words:1 ~pointer_words:1 x
      let to_message x = x.BA_.NM.StructStorage.data.MessageWrapper.Slice.msg
      let to_reader x = Some (RA_.StructStorage.readonly x)
      let init_root ?message_size () =
        BA_.alloc_root_struct ?message_size ~data_words:1 ~pointer_words:1 ()
      let init_pointer ptr =
        BA_.init_struct_pointer ptr ~data_words:1 ~pointer_words:1
    end
    module Clause = struct
      type struct_t = [`Clause_adb9aafdab430c1d]
      type t = struct_t builder_t
      let has_loc x =
        BA_.has_field x 0
      let loc_get x =
        BA_.get_struct ~data_words:0 ~pointer_words:2 x 0
      let loc_set_reader x v =
        BA_.set_struct ~data_words:0 ~pointer_words:2 x 0 v
      let loc_set_builder x v =
        BA_.set_struct ~data_words:0 ~pointer_words:2 x 0 (Some v)
      let loc_init x =
        BA_.init_struct ~data_words:0 ~pointer_words:2 x 0
      let has_text x =
        BA_.has_field x 1
      let text_get x =
        BA_.get_text ~default:"" x 1
      let text_set x v =
        BA_.set_text x 1 v
      let of_message x = BA_.get_root_struct ~data_words:0 ~pointer_words:2 x
      let to_message x = x.BA_.NM.StructStorage.data.MessageWrapper.Slice.msg
      let to_reader x = Some (RA_.StructStorage.readonly x)
      let init_root ?message_size () =
        BA_.alloc_root_struct ?message_size ~data_words:0 ~pointer_words:2 ()
      let init_pointer ptr =
        BA_.init_struct_pointer ptr ~data_words:0 ~pointer_words:2
    end
    module RecordKind = struct
      type t = RecordKind_12907431634679073908.t =
        | Struc
        | Class
        | Unio
        | Undefined of int
    end
    module Decl = struct
      type struct_t = [`Decl_d96c7f8624e22938]
      type t = struct_t builder_t
      module Param = struct
        type struct_t = [`Param_97bce41c55c2994a]
        type t = struct_t builder_t
        let has_type x =
          BA_.has_field x 0
        let type_get x =
          BA_.get_struct ~data_words:0 ~pointer_words:2 x 0
        let type_set_reader x v =
          BA_.set_struct ~data_words:0 ~pointer_words:2 x 0 v
        let type_set_builder x v =
          BA_.set_struct ~data_words:0 ~pointer_words:2 x 0 (Some v)
        let type_init x =
          BA_.init_struct ~data_words:0 ~pointer_words:2 x 0
        let has_name x =
          BA_.has_field x 1
        let name_get x =
          BA_.get_text ~default:"" x 1
        let name_set x v =
          BA_.set_text x 1 v
        let has_default x =
          BA_.has_field x 2
        let default_get x =
          BA_.get_struct ~data_words:0 ~pointer_words:2 x 2
        let default_set_reader x v =
          BA_.set_struct ~data_words:0 ~pointer_words:2 x 2 v
        let default_set_builder x v =
          BA_.set_struct ~data_words:0 ~pointer_words:2 x 2 (Some v)
        let default_init x =
          BA_.init_struct ~data_words:0 ~pointer_words:2 x 2
        let of_message x = BA_.get_root_struct ~data_words:0 ~pointer_words:3 x
        let to_message x = x.BA_.NM.StructStorage.data.MessageWrapper.Slice.msg
        let to_reader x = Some (RA_.StructStorage.readonly x)
        let init_root ?message_size () =
          BA_.alloc_root_struct ?message_size ~data_words:0 ~pointer_words:3 ()
        let init_pointer ptr =
          BA_.init_struct_pointer ptr ~data_words:0 ~pointer_words:3
      end
      module Var = struct
        type struct_t = [`Var_8da2907bb130c41c]
        type t = struct_t builder_t
        module InitStyle = struct
          type t = InitStyle_15285372864656172726.t =
            | CInit
            | CallInit
            | ListInit
            | Undefined of int
        end
        module VarInit = struct
          type struct_t = [`VarInit_96ff0430cb165092]
          type t = struct_t builder_t
          let has_init x =
            BA_.has_field x 0
          let init_get x =
            BA_.get_struct ~data_words:0 ~pointer_words:2 x 0
          let init_set_reader x v =
            BA_.set_struct ~data_words:0 ~pointer_words:2 x 0 v
          let init_set_builder x v =
            BA_.set_struct ~data_words:0 ~pointer_words:2 x 0 (Some v)
          let init_init x =
            BA_.init_struct ~data_words:0 ~pointer_words:2 x 0
          let style_get x =
            let discr = BA_.get_uint16 ~default:0 x 0 in
            InitStyle_15285372864656172726.decode discr
          let style_set x e =
            BA_.set_uint16 ~default:0 x 0 (InitStyle_15285372864656172726.encode_safe e)
          let style_set_unsafe x e =
            BA_.set_uint16 ~default:0 x 0 (InitStyle_15285372864656172726.encode_unsafe e)
          let of_message x = BA_.get_root_struct ~data_words:1 ~pointer_words:1 x
          let to_message x = x.BA_.NM.StructStorage.data.MessageWrapper.Slice.msg
          let to_reader x = Some (RA_.StructStorage.readonly x)
          let init_root ?message_size () =
            BA_.alloc_root_struct ?message_size ~data_words:1 ~pointer_words:1 ()
          let init_pointer ptr =
            BA_.init_struct_pointer ptr ~data_words:1 ~pointer_words:1
        end
        let has_name x =
          BA_.has_field x 0
        let name_get x =
          BA_.get_text ~default:"" x 0
        let name_set x v =
          BA_.set_text x 0 v
        let has_type x =
          BA_.has_field x 1
        let type_get x =
          BA_.get_struct ~data_words:0 ~pointer_words:2 x 1
        let type_set_reader x v =
          BA_.set_struct ~data_words:0 ~pointer_words:2 x 1 v
        let type_set_builder x v =
          BA_.set_struct ~data_words:0 ~pointer_words:2 x 1 (Some v)
        let type_init x =
          BA_.init_struct ~data_words:0 ~pointer_words:2 x 1
        let has_init x =
          BA_.has_field x 2
        let init_get x =
          BA_.get_struct ~data_words:1 ~pointer_words:1 x 2
        let init_set_reader x v =
          BA_.set_struct ~data_words:1 ~pointer_words:1 x 2 v
        let init_set_builder x v =
          BA_.set_struct ~data_words:1 ~pointer_words:1 x 2 (Some v)
        let init_init x =
          BA_.init_struct ~data_words:1 ~pointer_words:1 x 2
        let of_message x = BA_.get_root_struct ~data_words:0 ~pointer_words:3 x
        let to_message x = x.BA_.NM.StructStorage.data.MessageWrapper.Slice.msg
        let to_reader x = Some (RA_.StructStorage.readonly x)
        let init_root ?message_size () =
          BA_.alloc_root_struct ?message_size ~data_words:0 ~pointer_words:3 ()
        let init_pointer ptr =
          BA_.init_struct_pointer ptr ~data_words:0 ~pointer_words:3
      end
      module Function = struct
        type struct_t = [`Function_d64c65470b140c81]
        type t = struct_t builder_t
        let has_name x =
          BA_.has_field x 0
        let name_get x =
          BA_.get_text ~default:"" x 0
        let name_set x v =
          BA_.set_text x 0 v
        let has_body x =
          BA_.has_field x 1
        let body_get x =
          BA_.get_struct ~data_words:0 ~pointer_words:2 x 1
        let body_set_reader x v =
          BA_.set_struct ~data_words:0 ~pointer_words:2 x 1 v
        let body_set_builder x v =
          BA_.set_struct ~data_words:0 ~pointer_words:2 x 1 (Some v)
        let body_init x =
          BA_.init_struct ~data_words:0 ~pointer_words:2 x 1
        let has_result x =
          BA_.has_field x 2
        let result_get x =
          BA_.get_struct ~data_words:0 ~pointer_words:2 x 2
        let result_set_reader x v =
          BA_.set_struct ~data_words:0 ~pointer_words:2 x 2 v
        let result_set_builder x v =
          BA_.set_struct ~data_words:0 ~pointer_words:2 x 2 (Some v)
        let result_init x =
          BA_.init_struct ~data_words:0 ~pointer_words:2 x 2
        let has_params x =
          BA_.has_field x 3
        let params_get x = 
          BA_.get_struct_list ~data_words:0 ~pointer_words:3 x 3
        let params_get_list x =
          Capnp.Array.to_list (params_get x)
        let params_get_array x =
          Capnp.Array.to_array (params_get x)
        let params_set x v =
          BA_.set_struct_list ~data_words:0 ~pointer_words:3 x 3 v
        let params_init x n =
          BA_.init_struct_list ~data_words:0 ~pointer_words:3 x 3 n
        let params_set_list x v =
          let builder = params_init x (List.length v) in
          let () = List.iteri (fun i a -> Capnp.Array.set builder i a) v in
          builder
        let params_set_array x v =
          let builder = params_init x (Array.length v) in
          let () = Array.iteri (fun i a -> Capnp.Array.set builder i a) v in
          builder
        let has_contract x =
          BA_.has_field x 4
        let contract_get x = 
          BA_.get_struct_list ~data_words:0 ~pointer_words:2 x 4
        let contract_get_list x =
          Capnp.Array.to_list (contract_get x)
        let contract_get_array x =
          Capnp.Array.to_array (contract_get x)
        let contract_set x v =
          BA_.set_struct_list ~data_words:0 ~pointer_words:2 x 4 v
        let contract_init x n =
          BA_.init_struct_list ~data_words:0 ~pointer_words:2 x 4 n
        let contract_set_list x v =
          let builder = contract_init x (List.length v) in
          let () = List.iteri (fun i a -> Capnp.Array.set builder i a) v in
          builder
        let contract_set_array x v =
          let builder = contract_init x (Array.length v) in
          let () = Array.iteri (fun i a -> Capnp.Array.set builder i a) v in
          builder
        let of_message x = BA_.get_root_struct ~data_words:0 ~pointer_words:5 x
        let to_message x = x.BA_.NM.StructStorage.data.MessageWrapper.Slice.msg
        let to_reader x = Some (RA_.StructStorage.readonly x)
        let init_root ?message_size () =
          BA_.alloc_root_struct ?message_size ~data_words:0 ~pointer_words:5 ()
        let init_pointer ptr =
          BA_.init_struct_pointer ptr ~data_words:0 ~pointer_words:5
      end
      module Field = struct
        type struct_t = [`Field_ca43d1968400194b]
        type t = struct_t builder_t
        module InitStyle = struct
          type t = InitStyle_13739150215916644662.t =
            | CopyInit
            | ListInit
            | Undefined of int
        end
        module FieldInit = struct
          type struct_t = [`FieldInit_91afac6d2dc82432]
          type t = struct_t builder_t
          let has_init x =
            BA_.has_field x 0
          let init_get x =
            BA_.get_struct ~data_words:0 ~pointer_words:2 x 0
          let init_set_reader x v =
            BA_.set_struct ~data_words:0 ~pointer_words:2 x 0 v
          let init_set_builder x v =
            BA_.set_struct ~data_words:0 ~pointer_words:2 x 0 (Some v)
          let init_init x =
            BA_.init_struct ~data_words:0 ~pointer_words:2 x 0
          let style_get x =
            let discr = BA_.get_uint16 ~default:0 x 0 in
            InitStyle_13739150215916644662.decode discr
          let style_set x e =
            BA_.set_uint16 ~default:0 x 0 (InitStyle_13739150215916644662.encode_safe e)
          let style_set_unsafe x e =
            BA_.set_uint16 ~default:0 x 0 (InitStyle_13739150215916644662.encode_unsafe e)
          let of_message x = BA_.get_root_struct ~data_words:1 ~pointer_words:1 x
          let to_message x = x.BA_.NM.StructStorage.data.MessageWrapper.Slice.msg
          let to_reader x = Some (RA_.StructStorage.readonly x)
          let init_root ?message_size () =
            BA_.alloc_root_struct ?message_size ~data_words:1 ~pointer_words:1 ()
          let init_pointer ptr =
            BA_.init_struct_pointer ptr ~data_words:1 ~pointer_words:1
        end
        let has_name x =
          BA_.has_field x 0
        let name_get x =
          BA_.get_text ~default:"" x 0
        let name_set x v =
          BA_.set_text x 0 v
        let has_type x =
          BA_.has_field x 1
        let type_get x =
          BA_.get_struct ~data_words:0 ~pointer_words:2 x 1
        let type_set_reader x v =
          BA_.set_struct ~data_words:0 ~pointer_words:2 x 1 v
        let type_set_builder x v =
          BA_.set_struct ~data_words:0 ~pointer_words:2 x 1 (Some v)
        let type_init x =
          BA_.init_struct ~data_words:0 ~pointer_words:2 x 1
        let has_init x =
          BA_.has_field x 2
        let init_get x =
          BA_.get_struct ~data_words:1 ~pointer_words:1 x 2
        let init_set_reader x v =
          BA_.set_struct ~data_words:1 ~pointer_words:1 x 2 v
        let init_set_builder x v =
          BA_.set_struct ~data_words:1 ~pointer_words:1 x 2 (Some v)
        let init_init x =
          BA_.init_struct ~data_words:1 ~pointer_words:1 x 2
        let of_message x = BA_.get_root_struct ~data_words:0 ~pointer_words:3 x
        let to_message x = x.BA_.NM.StructStorage.data.MessageWrapper.Slice.msg
        let to_reader x = Some (RA_.StructStorage.readonly x)
        let init_root ?message_size () =
          BA_.alloc_root_struct ?message_size ~data_words:0 ~pointer_words:3 ()
        let init_pointer ptr =
          BA_.init_struct_pointer ptr ~data_words:0 ~pointer_words:3
      end
      module Record = struct
        type struct_t = [`Record_c925b09644ce72d3]
        type t = struct_t builder_t
        let has_name x =
          BA_.has_field x 0
        let name_get x =
          BA_.get_text ~default:"" x 0
        let name_set x v =
          BA_.set_text x 0 v
        let kind_get x =
          let discr = BA_.get_uint16 ~default:0 x 0 in
          RecordKind_12907431634679073908.decode discr
        let kind_set x e =
          BA_.set_uint16 ~default:0 x 0 (RecordKind_12907431634679073908.encode_safe e)
        let kind_set_unsafe x e =
          BA_.set_uint16 ~default:0 x 0 (RecordKind_12907431634679073908.encode_unsafe e)
        let has_fields x =
          BA_.has_field x 1
        let fields_get x = 
          BA_.get_struct_list ~data_words:0 ~pointer_words:2 x 1
        let fields_get_list x =
          Capnp.Array.to_list (fields_get x)
        let fields_get_array x =
          Capnp.Array.to_array (fields_get x)
        let fields_set x v =
          BA_.set_struct_list ~data_words:0 ~pointer_words:2 x 1 v
        let fields_init x n =
          BA_.init_struct_list ~data_words:0 ~pointer_words:2 x 1 n
        let fields_set_list x v =
          let builder = fields_init x (List.length v) in
          let () = List.iteri (fun i a -> Capnp.Array.set builder i a) v in
          builder
        let fields_set_array x v =
          let builder = fields_init x (Array.length v) in
          let () = Array.iteri (fun i a -> Capnp.Array.set builder i a) v in
          builder
        let has_methods x =
          BA_.has_field x 2
        let methods_get x = 
          BA_.get_struct_list ~data_words:0 ~pointer_words:2 x 2
        let methods_get_list x =
          Capnp.Array.to_list (methods_get x)
        let methods_get_array x =
          Capnp.Array.to_array (methods_get x)
        let methods_set x v =
          BA_.set_struct_list ~data_words:0 ~pointer_words:2 x 2 v
        let methods_init x n =
          BA_.init_struct_list ~data_words:0 ~pointer_words:2 x 2 n
        let methods_set_list x v =
          let builder = methods_init x (List.length v) in
          let () = List.iteri (fun i a -> Capnp.Array.set builder i a) v in
          builder
        let methods_set_array x v =
          let builder = methods_init x (Array.length v) in
          let () = Array.iteri (fun i a -> Capnp.Array.set builder i a) v in
          builder
        let has_def_get x =
          BA_.get_bit ~default:false x ~byte_ofs:2 ~bit_ofs:0
        let has_def_set x v =
          BA_.set_bit ~default:false x ~byte_ofs:2 ~bit_ofs:0 v
        let has_decls x =
          BA_.has_field x 3
        let decls_get x = 
          BA_.get_struct_list ~data_words:0 ~pointer_words:2 x 3
        let decls_get_list x =
          Capnp.Array.to_list (decls_get x)
        let decls_get_array x =
          Capnp.Array.to_array (decls_get x)
        let decls_set x v =
          BA_.set_struct_list ~data_words:0 ~pointer_words:2 x 3 v
        let decls_init x n =
          BA_.init_struct_list ~data_words:0 ~pointer_words:2 x 3 n
        let decls_set_list x v =
          let builder = decls_init x (List.length v) in
          let () = List.iteri (fun i a -> Capnp.Array.set builder i a) v in
          builder
        let decls_set_array x v =
          let builder = decls_init x (Array.length v) in
          let () = Array.iteri (fun i a -> Capnp.Array.set builder i a) v in
          builder
        let of_message x = BA_.get_root_struct ~data_words:1 ~pointer_words:4 x
        let to_message x = x.BA_.NM.StructStorage.data.MessageWrapper.Slice.msg
        let to_reader x = Some (RA_.StructStorage.readonly x)
        let init_root ?message_size () =
          BA_.alloc_root_struct ?message_size ~data_words:1 ~pointer_words:4 ()
        let init_pointer ptr =
          BA_.init_struct_pointer ptr ~data_words:1 ~pointer_words:4
      end
      module Method = struct
        type struct_t = [`Method_bebeef9161eb7d3c]
        type t = struct_t builder_t
        let static_get x =
          BA_.get_bit ~default:false x ~byte_ofs:0 ~bit_ofs:0
        let static_set x v =
          BA_.set_bit ~default:false x ~byte_ofs:0 ~bit_ofs:0 v
        let has_func x =
          BA_.has_field x 0
        let func_get x =
          BA_.get_struct ~data_words:0 ~pointer_words:5 x 0
        let func_set_reader x v =
          BA_.set_struct ~data_words:0 ~pointer_words:5 x 0 v
        let func_set_builder x v =
          BA_.set_struct ~data_words:0 ~pointer_words:5 x 0 (Some v)
        let func_init x =
          BA_.init_struct ~data_words:0 ~pointer_words:5 x 0
        let has_this x =
          BA_.has_field x 1
        let this_get x =
          BA_.get_struct ~data_words:1 ~pointer_words:1 x 1
        let this_set_reader x v =
          BA_.set_struct ~data_words:1 ~pointer_words:1 x 1 v
        let this_set_builder x v =
          BA_.set_struct ~data_words:1 ~pointer_words:1 x 1 (Some v)
        let this_init x =
          BA_.init_struct ~data_words:1 ~pointer_words:1 x 1
        let of_message x = BA_.get_root_struct ~data_words:1 ~pointer_words:2 x
        let to_message x = x.BA_.NM.StructStorage.data.MessageWrapper.Slice.msg
        let to_reader x = Some (RA_.StructStorage.readonly x)
        let init_root ?message_size () =
          BA_.alloc_root_struct ?message_size ~data_words:1 ~pointer_words:2 ()
        let init_pointer ptr =
          BA_.init_struct_pointer ptr ~data_words:1 ~pointer_words:2
      end
      module Typedef = struct
        type struct_t = [`Typedef_e46ae190d3365bca]
        type t = struct_t builder_t
        let has_type x =
          BA_.has_field x 0
        let type_get x =
          BA_.get_struct ~data_words:0 ~pointer_words:2 x 0
        let type_set_reader x v =
          BA_.set_struct ~data_words:0 ~pointer_words:2 x 0 v
        let type_set_builder x v =
          BA_.set_struct ~data_words:0 ~pointer_words:2 x 0 (Some v)
        let type_init x =
          BA_.init_struct ~data_words:0 ~pointer_words:2 x 0
        let has_name x =
          BA_.has_field x 1
        let name_get x =
          BA_.get_text ~default:"" x 1
        let name_set x v =
          BA_.set_text x 1 v
        let of_message x = BA_.get_root_struct ~data_words:0 ~pointer_words:2 x
        let to_message x = x.BA_.NM.StructStorage.data.MessageWrapper.Slice.msg
        let to_reader x = Some (RA_.StructStorage.readonly x)
        let init_root ?message_size () =
          BA_.alloc_root_struct ?message_size ~data_words:0 ~pointer_words:2 ()
        let init_pointer ptr =
          BA_.init_struct_pointer ptr ~data_words:0 ~pointer_words:2
      end
      module Enum = struct
        type struct_t = [`Enum_daecdb4dcd868ea8]
        type t = struct_t builder_t
        module EnumField = struct
          type struct_t = [`EnumField_87676bdbadd4545d]
          type t = struct_t builder_t
          let has_name x =
            BA_.has_field x 0
          let name_get x =
            BA_.get_text ~default:"" x 0
          let name_set x v =
            BA_.set_text x 0 v
          let has_expr x =
            BA_.has_field x 1
          let expr_get x =
            BA_.get_struct ~data_words:0 ~pointer_words:2 x 1
          let expr_set_reader x v =
            BA_.set_struct ~data_words:0 ~pointer_words:2 x 1 v
          let expr_set_builder x v =
            BA_.set_struct ~data_words:0 ~pointer_words:2 x 1 (Some v)
          let expr_init x =
            BA_.init_struct ~data_words:0 ~pointer_words:2 x 1
          let of_message x = BA_.get_root_struct ~data_words:0 ~pointer_words:2 x
          let to_message x = x.BA_.NM.StructStorage.data.MessageWrapper.Slice.msg
          let to_reader x = Some (RA_.StructStorage.readonly x)
          let init_root ?message_size () =
            BA_.alloc_root_struct ?message_size ~data_words:0 ~pointer_words:2 ()
          let init_pointer ptr =
            BA_.init_struct_pointer ptr ~data_words:0 ~pointer_words:2
        end
        let has_name x =
          BA_.has_field x 0
        let name_get x =
          BA_.get_text ~default:"" x 0
        let name_set x v =
          BA_.set_text x 0 v
        let has_fields x =
          BA_.has_field x 1
        let fields_get x = 
          BA_.get_struct_list ~data_words:0 ~pointer_words:2 x 1
        let fields_get_list x =
          Capnp.Array.to_list (fields_get x)
        let fields_get_array x =
          Capnp.Array.to_array (fields_get x)
        let fields_set x v =
          BA_.set_struct_list ~data_words:0 ~pointer_words:2 x 1 v
        let fields_init x n =
          BA_.init_struct_list ~data_words:0 ~pointer_words:2 x 1 n
        let fields_set_list x v =
          let builder = fields_init x (List.length v) in
          let () = List.iteri (fun i a -> Capnp.Array.set builder i a) v in
          builder
        let fields_set_array x v =
          let builder = fields_init x (Array.length v) in
          let () = Array.iteri (fun i a -> Capnp.Array.set builder i a) v in
          builder
        let of_message x = BA_.get_root_struct ~data_words:0 ~pointer_words:2 x
        let to_message x = x.BA_.NM.StructStorage.data.MessageWrapper.Slice.msg
        let to_reader x = Some (RA_.StructStorage.readonly x)
        let init_root ?message_size () =
          BA_.alloc_root_struct ?message_size ~data_words:0 ~pointer_words:2 ()
        let init_pointer ptr =
          BA_.init_struct_pointer ptr ~data_words:0 ~pointer_words:2
      end
      let union_not_initialized_get x = ()
      let union_not_initialized_set x =
        BA_.set_void ~discr:{BA_.Discr.value=0; BA_.Discr.byte_ofs=0} x
      let has_ann x =
        BA_.has_field x 0
      let ann_get x =
        BA_.get_text ~default:"" x 0
      let ann_set x v =
        BA_.set_text ~discr:{BA_.Discr.value=1; BA_.Discr.byte_ofs=0} x 0 v
      let empty_get x = ()
      let empty_set x =
        BA_.set_void ~discr:{BA_.Discr.value=2; BA_.Discr.byte_ofs=0} x
      let has_var x =
        BA_.has_field x 0
      let var_get x =
        BA_.get_struct ~data_words:0 ~pointer_words:3 x 0
      let var_set_reader x v =
        BA_.set_struct ~data_words:0 ~pointer_words:3 ~discr:{BA_.Discr.value=3; BA_.Discr.byte_ofs=0} x 0 v
      let var_set_builder x v =
        BA_.set_struct ~data_words:0 ~pointer_words:3 ~discr:{BA_.Discr.value=3; BA_.Discr.byte_ofs=0} x 0 (Some v)
      let var_init x =
        BA_.init_struct ~data_words:0 ~pointer_words:3 ~discr:{BA_.Discr.value=3; BA_.Discr.byte_ofs=0} x 0
      let has_function x =
        BA_.has_field x 0
      let function_get x =
        BA_.get_struct ~data_words:0 ~pointer_words:5 x 0
      let function_set_reader x v =
        BA_.set_struct ~data_words:0 ~pointer_words:5 ~discr:{BA_.Discr.value=4; BA_.Discr.byte_ofs=0} x 0 v
      let function_set_builder x v =
        BA_.set_struct ~data_words:0 ~pointer_words:5 ~discr:{BA_.Discr.value=4; BA_.Discr.byte_ofs=0} x 0 (Some v)
      let function_init x =
        BA_.init_struct ~data_words:0 ~pointer_words:5 ~discr:{BA_.Discr.value=4; BA_.Discr.byte_ofs=0} x 0
      let has_field x =
        BA_.has_field x 0
      let field_get x =
        BA_.get_struct ~data_words:0 ~pointer_words:3 x 0
      let field_set_reader x v =
        BA_.set_struct ~data_words:0 ~pointer_words:3 ~discr:{BA_.Discr.value=5; BA_.Discr.byte_ofs=0} x 0 v
      let field_set_builder x v =
        BA_.set_struct ~data_words:0 ~pointer_words:3 ~discr:{BA_.Discr.value=5; BA_.Discr.byte_ofs=0} x 0 (Some v)
      let field_init x =
        BA_.init_struct ~data_words:0 ~pointer_words:3 ~discr:{BA_.Discr.value=5; BA_.Discr.byte_ofs=0} x 0
      let has_record x =
        BA_.has_field x 0
      let record_get x =
        BA_.get_struct ~data_words:1 ~pointer_words:4 x 0
      let record_set_reader x v =
        BA_.set_struct ~data_words:1 ~pointer_words:4 ~discr:{BA_.Discr.value=6; BA_.Discr.byte_ofs=0} x 0 v
      let record_set_builder x v =
        BA_.set_struct ~data_words:1 ~pointer_words:4 ~discr:{BA_.Discr.value=6; BA_.Discr.byte_ofs=0} x 0 (Some v)
      let record_init x =
        BA_.init_struct ~data_words:1 ~pointer_words:4 ~discr:{BA_.Discr.value=6; BA_.Discr.byte_ofs=0} x 0
      let has_method x =
        BA_.has_field x 0
      let method_get x =
        BA_.get_struct ~data_words:1 ~pointer_words:2 x 0
      let method_set_reader x v =
        BA_.set_struct ~data_words:1 ~pointer_words:2 ~discr:{BA_.Discr.value=7; BA_.Discr.byte_ofs=0} x 0 v
      let method_set_builder x v =
        BA_.set_struct ~data_words:1 ~pointer_words:2 ~discr:{BA_.Discr.value=7; BA_.Discr.byte_ofs=0} x 0 (Some v)
      let method_init x =
        BA_.init_struct ~data_words:1 ~pointer_words:2 ~discr:{BA_.Discr.value=7; BA_.Discr.byte_ofs=0} x 0
      let access_spec_get x = ()
      let access_spec_set x =
        BA_.set_void ~discr:{BA_.Discr.value=8; BA_.Discr.byte_ofs=0} x
      let def_destructor_get x = ()
      let def_destructor_set x =
        BA_.set_void ~discr:{BA_.Discr.value=9; BA_.Discr.byte_ofs=0} x
      let def_constructor_get x = ()
      let def_constructor_set x =
        BA_.set_void ~discr:{BA_.Discr.value=10; BA_.Discr.byte_ofs=0} x
      let has_typedef x =
        BA_.has_field x 0
      let typedef_get x =
        BA_.get_struct ~data_words:0 ~pointer_words:2 x 0
      let typedef_set_reader x v =
        BA_.set_struct ~data_words:0 ~pointer_words:2 ~discr:{BA_.Discr.value=11; BA_.Discr.byte_ofs=0} x 0 v
      let typedef_set_builder x v =
        BA_.set_struct ~data_words:0 ~pointer_words:2 ~discr:{BA_.Discr.value=11; BA_.Discr.byte_ofs=0} x 0 (Some v)
      let typedef_init x =
        BA_.init_struct ~data_words:0 ~pointer_words:2 ~discr:{BA_.Discr.value=11; BA_.Discr.byte_ofs=0} x 0
      let has_enum_decl x =
        BA_.has_field x 0
      let enum_decl_get x =
        BA_.get_struct ~data_words:0 ~pointer_words:2 x 0
      let enum_decl_set_reader x v =
        BA_.set_struct ~data_words:0 ~pointer_words:2 ~discr:{BA_.Discr.value=12; BA_.Discr.byte_ofs=0} x 0 v
      let enum_decl_set_builder x v =
        BA_.set_struct ~data_words:0 ~pointer_words:2 ~discr:{BA_.Discr.value=12; BA_.Discr.byte_ofs=0} x 0 (Some v)
      let enum_decl_init x =
        BA_.init_struct ~data_words:0 ~pointer_words:2 ~discr:{BA_.Discr.value=12; BA_.Discr.byte_ofs=0} x 0
      type unnamed_union_t =
        | UnionNotInitialized
        | Ann of string
        | Empty
        | Var of [`Var_8da2907bb130c41c] builder_t
        | Function of [`Function_d64c65470b140c81] builder_t
        | Field of [`Field_ca43d1968400194b] builder_t
        | Record of [`Record_c925b09644ce72d3] builder_t
        | Method of [`Method_bebeef9161eb7d3c] builder_t
        | AccessSpec
        | DefDestructor
        | DefConstructor
        | Typedef of [`Typedef_e46ae190d3365bca] builder_t
        | EnumDecl of [`Enum_daecdb4dcd868ea8] builder_t
        | Undefined of int
      let get x =
        match BA_.get_uint16 ~default:0 x 0 with
        | 0 -> UnionNotInitialized
        | 1 -> Ann (ann_get x)
        | 2 -> Empty
        | 3 -> Var (var_get x)
        | 4 -> Function (function_get x)
        | 5 -> Field (field_get x)
        | 6 -> Record (record_get x)
        | 7 -> Method (method_get x)
        | 8 -> AccessSpec
        | 9 -> DefDestructor
        | 10 -> DefConstructor
        | 11 -> Typedef (typedef_get x)
        | 12 -> EnumDecl (enum_decl_get x)
        | v -> Undefined v
      let of_message x = BA_.get_root_struct ~data_words:1 ~pointer_words:1 x
      let to_message x = x.BA_.NM.StructStorage.data.MessageWrapper.Slice.msg
      let to_reader x = Some (RA_.StructStorage.readonly x)
      let init_root ?message_size () =
        BA_.alloc_root_struct ?message_size ~data_words:1 ~pointer_words:1 ()
      let init_pointer ptr =
        BA_.init_struct_pointer ptr ~data_words:1 ~pointer_words:1
    end
    module UnaryOpKind = struct
      type t = UnaryOpKind_16270584510146119878.t =
        | Plus
        | Minus
        | Not
        | LNot
        | AddrOf
        | Deref
        | PreInc
        | PreDec
        | PostInc
        | PostDec
        | Undefined of int
    end
    module BinaryOpKind = struct
      type t = BinaryOpKind_15775553773985184773.t =
        | Add
        | Sub
        | Assign
        | Mul
        | Div
        | Rem
        | Shl
        | Shr
        | Lt
        | Gt
        | Le
        | Ge
        | Eq
        | Ne
        | And
        | Or
        | Xor
        | LAnd
        | LOr
        | MulAssign
        | DivAssign
        | RemAssign
        | AddAssign
        | SubAssign
        | ShlAssign
        | ShrAssign
        | AndAssign
        | XorAssign
        | OrAssign
        | Undefined of int
    end
    module SufKind = struct
      type t = SufKind_10349718269051794478.t =
        | LSuf
        | LLSuf
        | NoSuf
        | Undefined of int
    end
    module NbBase = struct
      type t = NbBase_15750048951651279863.t =
        | Decimal
        | Octal
        | Hex
        | Undefined of int
    end
    module Expr = struct
      type struct_t = [`Expr_d5d009cc85c86562]
      type t = struct_t builder_t
      module UnaryOp = struct
        type struct_t = [`UnaryOp_b525d86a8f48e679]
        type t = struct_t builder_t
        let has_operand x =
          BA_.has_field x 0
        let operand_get x =
          BA_.get_struct ~data_words:0 ~pointer_words:2 x 0
        let operand_set_reader x v =
          BA_.set_struct ~data_words:0 ~pointer_words:2 x 0 v
        let operand_set_builder x v =
          BA_.set_struct ~data_words:0 ~pointer_words:2 x 0 (Some v)
        let operand_init x =
          BA_.init_struct ~data_words:0 ~pointer_words:2 x 0
        let kind_get x =
          let discr = BA_.get_uint16 ~default:0 x 0 in
          UnaryOpKind_16270584510146119878.decode discr
        let kind_set x e =
          BA_.set_uint16 ~default:0 x 0 (UnaryOpKind_16270584510146119878.encode_safe e)
        let kind_set_unsafe x e =
          BA_.set_uint16 ~default:0 x 0 (UnaryOpKind_16270584510146119878.encode_unsafe e)
        let of_message x = BA_.get_root_struct ~data_words:1 ~pointer_words:1 x
        let to_message x = x.BA_.NM.StructStorage.data.MessageWrapper.Slice.msg
        let to_reader x = Some (RA_.StructStorage.readonly x)
        let init_root ?message_size () =
          BA_.alloc_root_struct ?message_size ~data_words:1 ~pointer_words:1 ()
        let init_pointer ptr =
          BA_.init_struct_pointer ptr ~data_words:1 ~pointer_words:1
      end
      module BinaryOp = struct
        type struct_t = [`BinaryOp_b95e9a5df08d277c]
        type t = struct_t builder_t
        let has_lhs x =
          BA_.has_field x 0
        let lhs_get x =
          BA_.get_struct ~data_words:0 ~pointer_words:2 x 0
        let lhs_set_reader x v =
          BA_.set_struct ~data_words:0 ~pointer_words:2 x 0 v
        let lhs_set_builder x v =
          BA_.set_struct ~data_words:0 ~pointer_words:2 x 0 (Some v)
        let lhs_init x =
          BA_.init_struct ~data_words:0 ~pointer_words:2 x 0
        let has_rhs x =
          BA_.has_field x 1
        let rhs_get x =
          BA_.get_struct ~data_words:0 ~pointer_words:2 x 1
        let rhs_set_reader x v =
          BA_.set_struct ~data_words:0 ~pointer_words:2 x 1 v
        let rhs_set_builder x v =
          BA_.set_struct ~data_words:0 ~pointer_words:2 x 1 (Some v)
        let rhs_init x =
          BA_.init_struct ~data_words:0 ~pointer_words:2 x 1
        let kind_get x =
          let discr = BA_.get_uint16 ~default:0 x 0 in
          BinaryOpKind_15775553773985184773.decode discr
        let kind_set x e =
          BA_.set_uint16 ~default:0 x 0 (BinaryOpKind_15775553773985184773.encode_safe e)
        let kind_set_unsafe x e =
          BA_.set_uint16 ~default:0 x 0 (BinaryOpKind_15775553773985184773.encode_unsafe e)
        let of_message x = BA_.get_root_struct ~data_words:1 ~pointer_words:2 x
        let to_message x = x.BA_.NM.StructStorage.data.MessageWrapper.Slice.msg
        let to_reader x = Some (RA_.StructStorage.readonly x)
        let init_root ?message_size () =
          BA_.alloc_root_struct ?message_size ~data_words:1 ~pointer_words:2 ()
        let init_pointer ptr =
          BA_.init_struct_pointer ptr ~data_words:1 ~pointer_words:2
      end
      module IntLit = struct
        type struct_t = [`IntLit_a21731ff472a9631]
        type t = struct_t builder_t
        let has_value x =
          BA_.has_field x 0
        let value_get x =
          BA_.get_text ~default:"" x 0
        let value_set x v =
          BA_.set_text x 0 v
        let u_suffix_get x =
          BA_.get_bit ~default:false x ~byte_ofs:0 ~bit_ofs:0
        let u_suffix_set x v =
          BA_.set_bit ~default:false x ~byte_ofs:0 ~bit_ofs:0 v
        let l_suffix_get x =
          let discr = BA_.get_uint16 ~default:0 x 2 in
          SufKind_10349718269051794478.decode discr
        let l_suffix_set x e =
          BA_.set_uint16 ~default:0 x 2 (SufKind_10349718269051794478.encode_safe e)
        let l_suffix_set_unsafe x e =
          BA_.set_uint16 ~default:0 x 2 (SufKind_10349718269051794478.encode_unsafe e)
        let base_get x =
          let discr = BA_.get_uint16 ~default:0 x 4 in
          NbBase_15750048951651279863.decode discr
        let base_set x e =
          BA_.set_uint16 ~default:0 x 4 (NbBase_15750048951651279863.encode_safe e)
        let base_set_unsafe x e =
          BA_.set_uint16 ~default:0 x 4 (NbBase_15750048951651279863.encode_unsafe e)
        let of_message x = BA_.get_root_struct ~data_words:1 ~pointer_words:1 x
        let to_message x = x.BA_.NM.StructStorage.data.MessageWrapper.Slice.msg
        let to_reader x = Some (RA_.StructStorage.readonly x)
        let init_root ?message_size () =
          BA_.alloc_root_struct ?message_size ~data_words:1 ~pointer_words:1 ()
        let init_pointer ptr =
          BA_.init_struct_pointer ptr ~data_words:1 ~pointer_words:1
      end
      module Call = struct
        type struct_t = [`Call_d6c567dfeede9b58]
        type t = struct_t builder_t
        let has_args x =
          BA_.has_field x 0
        let args_get x = 
          BA_.get_struct_list ~data_words:0 ~pointer_words:2 x 0
        let args_get_list x =
          Capnp.Array.to_list (args_get x)
        let args_get_array x =
          Capnp.Array.to_array (args_get x)
        let args_set x v =
          BA_.set_struct_list ~data_words:0 ~pointer_words:2 x 0 v
        let args_init x n =
          BA_.init_struct_list ~data_words:0 ~pointer_words:2 x 0 n
        let args_set_list x v =
          let builder = args_init x (List.length v) in
          let () = List.iteri (fun i a -> Capnp.Array.set builder i a) v in
          builder
        let args_set_array x v =
          let builder = args_init x (Array.length v) in
          let () = Array.iteri (fun i a -> Capnp.Array.set builder i a) v in
          builder
        let has_callee x =
          BA_.has_field x 1
        let callee_get x =
          BA_.get_struct ~data_words:0 ~pointer_words:2 x 1
        let callee_set_reader x v =
          BA_.set_struct ~data_words:0 ~pointer_words:2 x 1 v
        let callee_set_builder x v =
          BA_.set_struct ~data_words:0 ~pointer_words:2 x 1 (Some v)
        let callee_init x =
          BA_.init_struct ~data_words:0 ~pointer_words:2 x 1
        let of_message x = BA_.get_root_struct ~data_words:0 ~pointer_words:2 x
        let to_message x = x.BA_.NM.StructStorage.data.MessageWrapper.Slice.msg
        let to_reader x = Some (RA_.StructStorage.readonly x)
        let init_root ?message_size () =
          BA_.alloc_root_struct ?message_size ~data_words:0 ~pointer_words:2 ()
        let init_pointer ptr =
          BA_.init_struct_pointer ptr ~data_words:0 ~pointer_words:2
      end
      module Member = struct
        type struct_t = [`Member_ab509764d68e7721]
        type t = struct_t builder_t
        let has_base x =
          BA_.has_field x 0
        let base_get x =
          BA_.get_struct ~data_words:0 ~pointer_words:2 x 0
        let base_set_reader x v =
          BA_.set_struct ~data_words:0 ~pointer_words:2 x 0 v
        let base_set_builder x v =
          BA_.set_struct ~data_words:0 ~pointer_words:2 x 0 (Some v)
        let base_init x =
          BA_.init_struct ~data_words:0 ~pointer_words:2 x 0
        let has_name x =
          BA_.has_field x 1
        let name_get x =
          BA_.get_text ~default:"" x 1
        let name_set x v =
          BA_.set_text x 1 v
        let arrow_get x =
          BA_.get_bit ~default:false x ~byte_ofs:0 ~bit_ofs:0
        let arrow_set x v =
          BA_.set_bit ~default:false x ~byte_ofs:0 ~bit_ofs:0 v
        let of_message x = BA_.get_root_struct ~data_words:1 ~pointer_words:2 x
        let to_message x = x.BA_.NM.StructStorage.data.MessageWrapper.Slice.msg
        let to_reader x = Some (RA_.StructStorage.readonly x)
        let init_root ?message_size () =
          BA_.alloc_root_struct ?message_size ~data_words:1 ~pointer_words:2 ()
        let init_pointer ptr =
          BA_.init_struct_pointer ptr ~data_words:1 ~pointer_words:2
      end
      module New = struct
        type struct_t = [`New_e0dbc3751d359960]
        type t = struct_t builder_t
        let has_type x =
          BA_.has_field x 0
        let type_get x =
          BA_.get_struct ~data_words:1 ~pointer_words:1 x 0
        let type_set_reader x v =
          BA_.set_struct ~data_words:1 ~pointer_words:1 x 0 v
        let type_set_builder x v =
          BA_.set_struct ~data_words:1 ~pointer_words:1 x 0 (Some v)
        let type_init x =
          BA_.init_struct ~data_words:1 ~pointer_words:1 x 0
        let has_expr x =
          BA_.has_field x 1
        let expr_get x =
          BA_.get_struct ~data_words:0 ~pointer_words:2 x 1
        let expr_set_reader x v =
          BA_.set_struct ~data_words:0 ~pointer_words:2 x 1 v
        let expr_set_builder x v =
          BA_.set_struct ~data_words:0 ~pointer_words:2 x 1 (Some v)
        let expr_init x =
          BA_.init_struct ~data_words:0 ~pointer_words:2 x 1
        let of_message x = BA_.get_root_struct ~data_words:0 ~pointer_words:2 x
        let to_message x = x.BA_.NM.StructStorage.data.MessageWrapper.Slice.msg
        let to_reader x = Some (RA_.StructStorage.readonly x)
        let init_root ?message_size () =
          BA_.alloc_root_struct ?message_size ~data_words:0 ~pointer_words:2 ()
        let init_pointer ptr =
          BA_.init_struct_pointer ptr ~data_words:0 ~pointer_words:2
      end
      let union_not_initialized_get x = ()
      let union_not_initialized_set x =
        BA_.set_void ~discr:{BA_.Discr.value=0; BA_.Discr.byte_ofs=0} x
      let has_unary_op x =
        BA_.has_field x 0
      let unary_op_get x =
        BA_.get_struct ~data_words:1 ~pointer_words:1 x 0
      let unary_op_set_reader x v =
        BA_.set_struct ~data_words:1 ~pointer_words:1 ~discr:{BA_.Discr.value=1; BA_.Discr.byte_ofs=0} x 0 v
      let unary_op_set_builder x v =
        BA_.set_struct ~data_words:1 ~pointer_words:1 ~discr:{BA_.Discr.value=1; BA_.Discr.byte_ofs=0} x 0 (Some v)
      let unary_op_init x =
        BA_.init_struct ~data_words:1 ~pointer_words:1 ~discr:{BA_.Discr.value=1; BA_.Discr.byte_ofs=0} x 0
      let has_binary_op x =
        BA_.has_field x 0
      let binary_op_get x =
        BA_.get_struct ~data_words:1 ~pointer_words:2 x 0
      let binary_op_set_reader x v =
        BA_.set_struct ~data_words:1 ~pointer_words:2 ~discr:{BA_.Discr.value=2; BA_.Discr.byte_ofs=0} x 0 v
      let binary_op_set_builder x v =
        BA_.set_struct ~data_words:1 ~pointer_words:2 ~discr:{BA_.Discr.value=2; BA_.Discr.byte_ofs=0} x 0 (Some v)
      let binary_op_init x =
        BA_.init_struct ~data_words:1 ~pointer_words:2 ~discr:{BA_.Discr.value=2; BA_.Discr.byte_ofs=0} x 0
      let bool_lit_get x =
        BA_.get_bit ~default:false x ~byte_ofs:2 ~bit_ofs:0
      let bool_lit_set x v =
        BA_.set_bit ~discr:{BA_.Discr.value=3; BA_.Discr.byte_ofs=0} ~default:false x ~byte_ofs:2 ~bit_ofs:0 v
      let has_int_lit x =
        BA_.has_field x 0
      let int_lit_get x =
        BA_.get_struct ~data_words:1 ~pointer_words:1 x 0
      let int_lit_set_reader x v =
        BA_.set_struct ~data_words:1 ~pointer_words:1 ~discr:{BA_.Discr.value=4; BA_.Discr.byte_ofs=0} x 0 v
      let int_lit_set_builder x v =
        BA_.set_struct ~data_words:1 ~pointer_words:1 ~discr:{BA_.Discr.value=4; BA_.Discr.byte_ofs=0} x 0 (Some v)
      let int_lit_init x =
        BA_.init_struct ~data_words:1 ~pointer_words:1 ~discr:{BA_.Discr.value=4; BA_.Discr.byte_ofs=0} x 0
      let has_string_lit x =
        BA_.has_field x 0
      let string_lit_get x =
        BA_.get_text ~default:"" x 0
      let string_lit_set x v =
        BA_.set_text ~discr:{BA_.Discr.value=5; BA_.Discr.byte_ofs=0} x 0 v
      let has_call x =
        BA_.has_field x 0
      let call_get x =
        BA_.get_struct ~data_words:0 ~pointer_words:2 x 0
      let call_set_reader x v =
        BA_.set_struct ~data_words:0 ~pointer_words:2 ~discr:{BA_.Discr.value=6; BA_.Discr.byte_ofs=0} x 0 v
      let call_set_builder x v =
        BA_.set_struct ~data_words:0 ~pointer_words:2 ~discr:{BA_.Discr.value=6; BA_.Discr.byte_ofs=0} x 0 (Some v)
      let call_init x =
        BA_.init_struct ~data_words:0 ~pointer_words:2 ~discr:{BA_.Discr.value=6; BA_.Discr.byte_ofs=0} x 0
      let has_decl_ref x =
        BA_.has_field x 0
      let decl_ref_get x =
        BA_.get_text ~default:"" x 0
      let decl_ref_set x v =
        BA_.set_text ~discr:{BA_.Discr.value=7; BA_.Discr.byte_ofs=0} x 0 v
      let has_member x =
        BA_.has_field x 0
      let member_get x =
        BA_.get_struct ~data_words:1 ~pointer_words:2 x 0
      let member_set_reader x v =
        BA_.set_struct ~data_words:1 ~pointer_words:2 ~discr:{BA_.Discr.value=8; BA_.Discr.byte_ofs=0} x 0 v
      let member_set_builder x v =
        BA_.set_struct ~data_words:1 ~pointer_words:2 ~discr:{BA_.Discr.value=8; BA_.Discr.byte_ofs=0} x 0 (Some v)
      let member_init x =
        BA_.init_struct ~data_words:1 ~pointer_words:2 ~discr:{BA_.Discr.value=8; BA_.Discr.byte_ofs=0} x 0
      let this_get x = ()
      let this_set x =
        BA_.set_void ~discr:{BA_.Discr.value=9; BA_.Discr.byte_ofs=0} x
      let has_member_call x =
        BA_.has_field x 0
      let member_call_get x =
        BA_.get_struct ~data_words:0 ~pointer_words:2 x 0
      let member_call_set_reader x v =
        BA_.set_struct ~data_words:0 ~pointer_words:2 ~discr:{BA_.Discr.value=10; BA_.Discr.byte_ofs=0} x 0 v
      let member_call_set_builder x v =
        BA_.set_struct ~data_words:0 ~pointer_words:2 ~discr:{BA_.Discr.value=10; BA_.Discr.byte_ofs=0} x 0 (Some v)
      let member_call_init x =
        BA_.init_struct ~data_words:0 ~pointer_words:2 ~discr:{BA_.Discr.value=10; BA_.Discr.byte_ofs=0} x 0
      let has_new x =
        BA_.has_field x 0
      let new_get x =
        BA_.get_struct ~data_words:0 ~pointer_words:2 x 0
      let new_set_reader x v =
        BA_.set_struct ~data_words:0 ~pointer_words:2 ~discr:{BA_.Discr.value=11; BA_.Discr.byte_ofs=0} x 0 v
      let new_set_builder x v =
        BA_.set_struct ~data_words:0 ~pointer_words:2 ~discr:{BA_.Discr.value=11; BA_.Discr.byte_ofs=0} x 0 (Some v)
      let new_init x =
        BA_.init_struct ~data_words:0 ~pointer_words:2 ~discr:{BA_.Discr.value=11; BA_.Discr.byte_ofs=0} x 0
      let has_construct x =
        BA_.has_field x 0
      let construct_get x = 
        BA_.get_struct_list ~data_words:0 ~pointer_words:2 x 0
      let construct_get_list x =
        Capnp.Array.to_list (construct_get x)
      let construct_get_array x =
        Capnp.Array.to_array (construct_get x)
      let construct_set x v =
        BA_.set_struct_list ~data_words:0 ~pointer_words:2 ~discr:{BA_.Discr.value=12; BA_.Discr.byte_ofs=0} x 0 v
      let construct_init x n =
        BA_.init_struct_list ~data_words:0 ~pointer_words:2 ~discr:{BA_.Discr.value=12; BA_.Discr.byte_ofs=0} x 0 n
      let construct_set_list x v =
        let builder = construct_init x (List.length v) in
        let () = List.iteri (fun i a -> Capnp.Array.set builder i a) v in
        builder
      let construct_set_array x v =
        let builder = construct_init x (Array.length v) in
        let () = Array.iteri (fun i a -> Capnp.Array.set builder i a) v in
        builder
      let null_ptr_lit_get x = ()
      let null_ptr_lit_set x =
        BA_.set_void ~discr:{BA_.Discr.value=13; BA_.Discr.byte_ofs=0} x
      type unnamed_union_t =
        | UnionNotInitialized
        | UnaryOp of [`UnaryOp_b525d86a8f48e679] builder_t
        | BinaryOp of [`BinaryOp_b95e9a5df08d277c] builder_t
        | BoolLit of bool
        | IntLit of [`IntLit_a21731ff472a9631] builder_t
        | StringLit of string
        | Call of [`Call_d6c567dfeede9b58] builder_t
        | DeclRef of string
        | Member of [`Member_ab509764d68e7721] builder_t
        | This
        | MemberCall of [`Call_d6c567dfeede9b58] builder_t
        | New of [`New_e0dbc3751d359960] builder_t
        | Construct of (rw, Node.t, array_t) Capnp.Array.t
        | NullPtrLit
        | Undefined of int
      let get x =
        match BA_.get_uint16 ~default:0 x 0 with
        | 0 -> UnionNotInitialized
        | 1 -> UnaryOp (unary_op_get x)
        | 2 -> BinaryOp (binary_op_get x)
        | 3 -> BoolLit (bool_lit_get x)
        | 4 -> IntLit (int_lit_get x)
        | 5 -> StringLit (string_lit_get x)
        | 6 -> Call (call_get x)
        | 7 -> DeclRef (decl_ref_get x)
        | 8 -> Member (member_get x)
        | 9 -> This
        | 10 -> MemberCall (member_call_get x)
        | 11 -> New (new_get x)
        | 12 -> Construct (construct_get x)
        | 13 -> NullPtrLit
        | v -> Undefined v
      let of_message x = BA_.get_root_struct ~data_words:1 ~pointer_words:1 x
      let to_message x = x.BA_.NM.StructStorage.data.MessageWrapper.Slice.msg
      let to_reader x = Some (RA_.StructStorage.readonly x)
      let init_root ?message_size () =
        BA_.alloc_root_struct ?message_size ~data_words:1 ~pointer_words:1 ()
      let init_pointer ptr =
        BA_.init_struct_pointer ptr ~data_words:1 ~pointer_words:1
    end
    module TU = struct
      type struct_t = [`TU_c63033d95787d2ff]
      type t = struct_t builder_t
      module FileEntry = struct
        type struct_t = [`FileEntry_8f25ab49a7ca891f]
        type t = struct_t builder_t
        let fd_get x =
          BA_.get_uint16 ~default:0 x 0
        let fd_set_exn x v =
          BA_.set_uint16 ~default:0 x 0 v
        let has_name x =
          BA_.has_field x 0
        let name_get x =
          BA_.get_text ~default:"" x 0
        let name_set x v =
          BA_.set_text x 0 v
        let of_message x = BA_.get_root_struct ~data_words:1 ~pointer_words:1 x
        let to_message x = x.BA_.NM.StructStorage.data.MessageWrapper.Slice.msg
        let to_reader x = Some (RA_.StructStorage.readonly x)
        let init_root ?message_size () =
          BA_.alloc_root_struct ?message_size ~data_words:1 ~pointer_words:1 ()
        let init_pointer ptr =
          BA_.init_struct_pointer ptr ~data_words:1 ~pointer_words:1
      end
      let has_decls x =
        BA_.has_field x 0
      let decls_get x = 
        BA_.get_struct_list ~data_words:0 ~pointer_words:2 x 0
      let decls_get_list x =
        Capnp.Array.to_list (decls_get x)
      let decls_get_array x =
        Capnp.Array.to_array (decls_get x)
      let decls_set x v =
        BA_.set_struct_list ~data_words:0 ~pointer_words:2 x 0 v
      let decls_init x n =
        BA_.init_struct_list ~data_words:0 ~pointer_words:2 x 0 n
      let decls_set_list x v =
        let builder = decls_init x (List.length v) in
        let () = List.iteri (fun i a -> Capnp.Array.set builder i a) v in
        builder
      let decls_set_array x v =
        let builder = decls_init x (Array.length v) in
        let () = Array.iteri (fun i a -> Capnp.Array.set builder i a) v in
        builder
      let has_files x =
        BA_.has_field x 1
      let files_get x = 
        BA_.get_struct_list ~data_words:1 ~pointer_words:1 x 1
      let files_get_list x =
        Capnp.Array.to_list (files_get x)
      let files_get_array x =
        Capnp.Array.to_array (files_get x)
      let files_set x v =
        BA_.set_struct_list ~data_words:1 ~pointer_words:1 x 1 v
      let files_init x n =
        BA_.init_struct_list ~data_words:1 ~pointer_words:1 x 1 n
      let files_set_list x v =
        let builder = files_init x (List.length v) in
        let () = List.iteri (fun i a -> Capnp.Array.set builder i a) v in
        builder
      let files_set_array x v =
        let builder = files_init x (Array.length v) in
        let () = Array.iteri (fun i a -> Capnp.Array.set builder i a) v in
        builder
      let of_message x = BA_.get_root_struct ~data_words:0 ~pointer_words:2 x
      let to_message x = x.BA_.NM.StructStorage.data.MessageWrapper.Slice.msg
      let to_reader x = Some (RA_.StructStorage.readonly x)
      let init_root ?message_size () =
        BA_.alloc_root_struct ?message_size ~data_words:0 ~pointer_words:2 ()
      let init_pointer ptr =
        BA_.init_struct_pointer ptr ~data_words:0 ~pointer_words:2
    end
    module Err = struct
      type struct_t = [`Err_9162b284a3cba818]
      type t = struct_t builder_t
      let has_loc x =
        BA_.has_field x 0
      let loc_get x =
        BA_.get_struct ~data_words:0 ~pointer_words:2 x 0
      let loc_set_reader x v =
        BA_.set_struct ~data_words:0 ~pointer_words:2 x 0 v
      let loc_set_builder x v =
        BA_.set_struct ~data_words:0 ~pointer_words:2 x 0 (Some v)
      let loc_init x =
        BA_.init_struct ~data_words:0 ~pointer_words:2 x 0
      let has_reason x =
        BA_.has_field x 1
      let reason_get x =
        BA_.get_text ~default:"" x 1
      let reason_set x v =
        BA_.set_text x 1 v
      let of_message x = BA_.get_root_struct ~data_words:0 ~pointer_words:2 x
      let to_message x = x.BA_.NM.StructStorage.data.MessageWrapper.Slice.msg
      let to_reader x = Some (RA_.StructStorage.readonly x)
      let init_root ?message_size () =
        BA_.alloc_root_struct ?message_size ~data_words:0 ~pointer_words:2 ()
      let init_pointer ptr =
        BA_.init_struct_pointer ptr ~data_words:0 ~pointer_words:2
    end
    module SerResult = struct
      type struct_t = [`SerResult_a5cc2b3709c2654d]
      type t = struct_t builder_t
      let ok_get x = ()
      let ok_set x =
        BA_.set_void ~discr:{BA_.Discr.value=0; BA_.Discr.byte_ofs=0} x
      let err_get x = ()
      let err_set x =
        BA_.set_void ~discr:{BA_.Discr.value=1; BA_.Discr.byte_ofs=0} x
      type unnamed_union_t =
        | Ok
        | Err
        | Undefined of int
      let get x =
        match BA_.get_uint16 ~default:0 x 0 with
        | 0 -> Ok
        | 1 -> Err
        | v -> Undefined v
      let of_message x = BA_.get_root_struct ~data_words:1 ~pointer_words:0 x
      let to_message x = x.BA_.NM.StructStorage.data.MessageWrapper.Slice.msg
      let to_reader x = Some (RA_.StructStorage.readonly x)
      let init_root ?message_size () =
        BA_.alloc_root_struct ?message_size ~data_words:1 ~pointer_words:0 ()
      let init_pointer ptr =
        BA_.init_struct_pointer ptr ~data_words:1 ~pointer_words:0
    end
  end

  module Client = struct
  end

  module Service = struct
  end
  module MessageWrapper = MessageWrapper
end [@@inline]

module Make(M:Capnp.MessageSig.S) = MakeRPC[@inlined](Capnp.RPC.None(M)) [@@inline]
