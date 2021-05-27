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

module MakeRPC(MessageWrapper : Capnp.RPC.S) : sig
  include S with module MessageWrapper = MessageWrapper

  module Client : sig
  end

  module Service : sig
  end
end

module Make(M : Capnp.MessageSig.S) : module type of MakeRPC(Capnp.RPC.None(M))
