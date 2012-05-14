open Assertions

module VerifyExpr :
  functor (VerifyProgramArgs : Verifast1.VERIFY_PROGRAM_ARGS) ->
    sig
      include module type of Assertions(VerifyProgramArgs)
      val meths_impl : (string * Lexer.loc) list ref
      val cons_impl : (string * Lexer.loc) list ref
      module CheckFile_VerifyExpr :
        functor (CheckFileArgs : CHECK_FILE_ARGS) ->
          sig
            include module type of CheckFile_Assertions(CheckFileArgs)
            val block_assigned_variables : Ast.stmt list -> string list
            val expr_assigned_variables : Ast.expr -> string list
            val assigned_variables : Ast.stmt -> string list
            val dummypat : 'a Verifast0.pat0
            val get_points_to :
              termnode Verifast0.heap ->
              termnode ->
              termnode ->
              Lexer.loc ->
              (termnode Verifast0.chunk list ->
               termnode -> termnode -> Verifast0.symexec_result) ->
              Verifast0.symexec_result
            val get_field :
              termnode Verifast0.heap ->
              termnode ->
              string ->
              string ->
              Lexer.loc ->
              (termnode Verifast0.chunk list ->
               termnode -> termnode -> Verifast0.symexec_result) ->
              Verifast0.symexec_result
            val current_thread_name : string
            val current_thread_type : Ast.type_
            val functypemap1 :
              (string *
               (Lexer.loc * Ast.ghostness * string list * Ast.type_ option *
                (string * Ast.type_) list * (string * Ast.type_) list *
                Ast.asn * Ast.asn *
                (string *
                 (Lexer.loc * string list * int * Ast.type_ list * termnode *
                  int option))
                list))
              list
            val functypemap : (string * func_type_info) list
            val check_breakpoint :
              'a ->
              'b -> ((string * string) * int * int) * Lexer.srcpos -> unit
            val is_empty_chunk :
              termnode * bool ->
              Ast.type_ list -> 'a -> termnode list -> bool
            val check_leaks :
              termnode Verifast0.heap ->
              termnode Verifast0.env ->
              Lexer.loc -> string -> Verifast0.symexec_result
            val check_func_header_compat :
              Lexer.loc ->
              string ->
              (string * termnode) list ->
              Ast.func_kind * string list * Ast.type_ option *
              (string * Ast.type_) list * 'a * Ast.asn * Ast.asn *
              (Ast.type_ * Ast.asn) list ->
              Ast.func_kind * string list * Ast.type_ option *
              (string * Ast.type_) list * 'a * (string * Ast.type_) list *
              (string * termnode) list * Ast.asn * Ast.asn *
              (Ast.type_ * Ast.asn) list -> unit
            val assume_is_functype : string -> string -> unit
            val functypes_implemented :
              (string * Lexer.loc * string * string list * bool) list ref
            val check_func_header :
              string ->
              Ast.import list ->
              string list ->
              (string * Ast.type_) list ->
              (string * termnode) list ->
              Lexer.loc ->
              Ast.func_kind ->
              string list ->
              Ast.type_expr option ->
              string ->
              termnode option ->
              (Ast.type_expr * string) list ->
              bool ->
              (string * Ast.type_expr list * (Lexer.loc * string) list)
              option ->
              (Ast.asn * Ast.asn) option ->
              'a option ->
              Ast.type_ option * (string * Ast.type_) list *
              (string * pred_fam_info map * Ast.type_ list *
               (Lexer.loc * string) list)
              option * Ast.asn * (string * Ast.type_) list * Ast.asn
            val funcmap1 : (string * func_info) list
            val prototypes_implemented : (string * Lexer.loc) list
            val funcmap : (string * func_info) list
            val interfmap1 : (string * interface_info) list
            val string_of_sign : string * Ast.type_ list -> string
            val interfmap : interface_info map
            val dynamic_of : Ast.asn -> Ast.asn
            val classmap1 : (string * class_info) list
            val classmap : (string * class_info) list
            val mark_if_local :
              ('a list ref * ('a * bool ref) list) list -> 'a -> unit
            val expr_mark_addr_taken :
              Ast.expr ->
              (string list ref * (string * bool ref) list) list -> unit
            val pat_expr_mark_addr_taken :
              Ast.pat ->
              (string list ref * (string * bool ref) list) list -> unit
            val ass_mark_addr_taken :
              Ast.asn ->
              (string list ref * (string * bool ref) list) list -> unit
            val stmt_mark_addr_taken :
              Ast.stmt ->
              (string list ref * (string * bool ref) list) list ->
              ((string list ref * (string * bool ref) list) list -> unit) ->
              unit
            val stmts_mark_addr_taken :
              Ast.stmt list ->
              (string list ref * (string * bool ref) list) list ->
              ((string list ref * (string * bool ref) list) list -> unit) ->
              unit
            val expr_address_taken : Ast.expr -> string list
            val stmt_address_taken : Ast.stmt -> string list
            val nonempty_pred_symbs : termnode list
            val eval_non_pure_cps :
              (termnode Verifast0.chunk list * 'a ->
               Ast.expr ->
               (termnode Verifast0.chunk list * 'a -> termnode -> 'b) -> 'b) ->
              bool ->
              termnode Verifast0.chunk list * 'a ->
              (string * termnode) list ->
              Ast.expr ->
              (termnode Verifast0.chunk list * 'a -> termnode -> 'b) -> 'b
            val eval_non_pure :
              bool ->
              termnode Verifast0.chunk list ->
              (string * termnode) list -> Ast.expr -> termnode
            val produce_c_object :
              Lexer.loc ->
              termnode ->
              termnode ->
              Ast.type_ ->
              Ast.expr option option ->
              bool ->
              bool ->
              termnode Verifast0.chunk list ->
              (termnode Verifast0.chunk list -> Verifast0.symexec_result) ->
              Verifast0.symexec_result
            val consume_c_object :
              Lexer.loc ->
              termnode ->
              Ast.type_ ->
              termnode Verifast0.heap ->
              bool ->
              (termnode Verifast0.heap -> Verifast0.symexec_result) ->
              Verifast0.symexec_result
            val assume_is_of_type :
              Lexer.loc ->
              termnode ->
              Ast.type_ ->
              (unit -> Verifast0.symexec_result) -> Verifast0.symexec_result
            val verify_call :
              (string * func_info) list ->
              (termnode Verifast0.heap ->
               termnode Verifast0.env ->
               Ast.expr ->
               (termnode Verifast0.heap ->
                termnode Verifast0.env ->
                termnode -> Verifast0.symexec_result) ->
               Verifast0.symexec_result) ->
              Lexer.loc ->
              string * Ast.import list ->
              string option ->
              'a option ->
              Ast.type_ list ->
              termnode Verifast0.pat0 list ->
              string list * Ast.type_ option * (string * Ast.type_) list *
              (string * termnode) list * Ast.asn * Ast.asn *
              (Ast.type_ * Ast.asn) list option * 'b ->
              bool ->
              ('a list * 'a * string option) option ->
              (termnode * int) list ->
              termnode Verifast0.heap ->
              string list ->
              (string * Ast.type_) list ->
              string list ->
              termnode Verifast0.env ->
              (termnode Verifast0.heap ->
               termnode Verifast0.env -> termnode -> Verifast0.symexec_result) ->
              (Lexer.loc ->
               termnode Verifast0.heap ->
               termnode Verifast0.env ->
               Ast.type_ -> termnode -> Verifast0.symexec_result) ->
              Verifast0.symexec_result
            val funcnameterm_of : ('a * func_info) list -> 'a -> termnode
            val default_value : Ast.type_ -> termnode
            module LValues :
              sig
                type lvalue =
                    Var of Lexer.loc * string * Ast.ident_scope option ref
                  | Field of Lexer.loc * termnode option * string * string *
                      Ast.type_ * Ast.constant_value option option ref *
                      Ast.ghostness * termnode
                  | ArrayElement of Lexer.loc * termnode * Ast.type_ *
                      termnode
                  | Deref of Lexer.loc * termnode * Ast.type_
              end
            val verify_expr :
              bool * bool ->
              string * Ast.import list ->
              string list ->
              bool ->
              (string list * string * string option) option ->
              (string * func_info) list ->
              (termnode * int) list ->
              (string * Ast.type_) list ->
              string list ->
              termnode Verifast0.heap ->
              termnode Verifast0.env ->
              string option ->
              Ast.expr ->
              (termnode Verifast0.heap ->
               termnode Verifast0.env -> termnode -> Verifast0.symexec_result) ->
              (Lexer.loc ->
               termnode Verifast0.heap ->
               termnode Verifast0.env ->
               Ast.type_ -> termnode -> Verifast0.symexec_result) ->
              Verifast0.symexec_result
          end
    end
