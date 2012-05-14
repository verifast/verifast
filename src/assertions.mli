open Verifast1

module Assertions :
  functor (VerifyProgramArgs : Verifast1.VERIFY_PROGRAM_ARGS) ->
    sig
      include module type of VerifyProgram1(VerifyProgramArgs)
      type auto_lemma_info =
          string option * string list * string list * string list * Ast.asn *
          Ast.asn
      val auto_lemmas : (string, auto_lemma_info) Hashtbl.t
      module CheckFile_Assertions :
        functor (CheckFileArgs : CHECK_FILE_ARGS) ->
          sig
            include module type of CheckFile1(CheckFileArgs)
            val assert_expr :
              'a ->
              Ast.expr ->
              'b ->
              (string * termnode) list ->
              Lexer.loc -> string -> string option -> unit
            val success : unit -> Verifast0.symexec_result
            val branch :
              (unit -> Verifast0.symexec_result) ->
              (unit -> Verifast0.symexec_result) -> Verifast0.symexec_result
            val assert_expr_split :
              Ast.expr ->
              termnode Verifast0.heap ->
              termnode Verifast0.env ->
              Lexer.loc ->
              string -> string option -> Verifast0.symexec_result
            val evalpat :
              bool ->
              string list ->
              (string * termnode) list ->
              Ast.pat ->
              Ast.type_ ->
              Ast.type_ ->
              (string list -> (string * termnode) list -> termnode -> 'a) ->
              'a
            val evalpats :
              string list ->
              (string * termnode) list ->
              Ast.pat list ->
              Ast.type_ list ->
              Ast.type_ list ->
              (string list -> (string * termnode) list -> termnode list -> 'a) ->
              'a
            val real_mul : 'a -> termnode -> termnode -> termnode
            val real_div : Lexer.loc -> 'a -> termnode -> 'a
            val definitely_equal : termnode -> termnode -> bool
            val predname_eq : termnode * bool -> termnode * bool -> bool
            val assume_field :
              termnode Verifast0.chunk list ->
              string ->
              string ->
              Ast.type_ ->
              Ast.ghostness ->
              termnode ->
              termnode ->
              termnode ->
              (termnode Verifast0.chunk list -> Verifast0.symexec_result) ->
              Verifast0.symexec_result
            val produce_chunk :
              termnode Verifast0.chunk list ->
              termnode * bool ->
              Ast.type_ list ->
              termnode ->
              int option ->
              termnode list ->
              Verifast0.chunk_info option ->
              (termnode Verifast0.chunk list -> Verifast0.symexec_result) ->
              Verifast0.symexec_result
            val produce_asn_core :
              (string * Ast.type_) list ->
              termnode Verifast0.heap ->
              string list ->
              termnode Verifast0.env ->
              Ast.asn ->
              termnode ->
              Verifast0.chunk_info option ->
              Verifast0.chunk_info option ->
              bool ->
              (termnode Verifast0.heap ->
               string list ->
               termnode Verifast0.env -> Verifast0.symexec_result) ->
              Verifast0.symexec_result
            val produce_asn :
              (string * Ast.type_) list ->
              termnode Verifast0.heap ->
              string list ->
              termnode Verifast0.env ->
              Ast.asn ->
              termnode ->
              Verifast0.chunk_info option ->
              Verifast0.chunk_info option ->
              (termnode Verifast0.heap ->
               string list ->
               termnode Verifast0.env -> Verifast0.symexec_result) ->
              Verifast0.symexec_result
            val match_chunk :
              string list ->
              'a ->
              (string * termnode) list ->
              (string * termnode) list ->
              Lexer.loc ->
              termnode * bool ->
              Ast.type_ list ->
              termnode ->
              termnode Verifast0.pat0 ->
              int option ->
              termnode Verifast0.pat0 list ->
              Ast.type_ list ->
              Ast.type_ list ->
              termnode Verifast0.chunk ->
              (termnode Verifast0.chunk * termnode * termnode list *
               Verifast0.chunk_info option * string list *
               (string * termnode) list * (string * termnode) list *
               termnode Verifast0.chunk list)
              option
            val lookup_points_to_chunk_core :
              termnode Verifast0.chunk list ->
              termnode -> termnode -> termnode option
            val lookup_points_to_chunk :
              termnode Verifast0.chunk list ->
              'a -> Lexer.loc -> termnode -> termnode -> termnode
            val read_field :
              termnode Verifast0.chunk list ->
              'a -> Lexer.loc -> termnode -> string -> string -> termnode
            val read_static_field :
              termnode Verifast0.chunk list ->
              'a -> Lexer.loc -> string -> string -> termnode
            val try_read_java_array :
              termnode Verifast0.chunk list ->
              'a -> 'b -> termnode -> termnode -> 'c -> termnode option
            val try_update_java_array :
              termnode Verifast0.chunk list ->
              'a ->
              'b ->
              termnode ->
              termnode ->
              'c -> termnode -> termnode Verifast0.chunk list option
            val read_java_array :
              termnode Verifast0.chunk list ->
              'a -> Lexer.loc -> termnode -> termnode -> 'b -> termnode
            val pointer_pred_symb : unit -> termnode
            val int_pred_symb : unit -> termnode
            val u_int_pred_symb : unit -> termnode
            val char_pred_symb : unit -> termnode
            val u_char_pred_symb : unit -> termnode
            val try_pointee_pred_symb : Ast.type_ -> termnode option
            val pointee_pred_symb : Lexer.loc -> Ast.type_ -> termnode
            val read_c_array :
              termnode Verifast0.chunk list ->
              'a ->
              Lexer.loc -> termnode -> termnode -> Ast.type_ -> termnode
            val read_array :
              termnode Verifast0.chunk list ->
              'a ->
              Lexer.loc -> termnode -> termnode -> Ast.type_ -> termnode
            val deref_pointer :
              termnode Verifast0.chunk list ->
              'a -> Lexer.loc -> termnode -> Ast.type_ -> termnode
            val lists_disjoint : 'a list -> 'a list -> bool
            val with_updated_ref : 'a ref -> ('a -> 'a) -> (unit -> 'b) -> 'b
            val consume_chunk_recursion_depth : int ref
            val consume_chunk_core :
              (termnode *
               (termnode Verifast0.heap ->
                Ast.type_ list ->
                bool ->
                termnode list -> (termnode Verifast0.heap option -> 'a) -> 'a)
               list)
              list ->
              termnode Verifast0.heap ->
              string list ->
              termnode Verifast0.env ->
              (string * termnode) list ->
              Lexer.loc ->
              termnode * bool ->
              Ast.type_ list ->
              termnode ->
              termnode Verifast0.pat0 ->
              int option ->
              termnode Verifast0.pat0 list ->
              Ast.type_ list ->
              Ast.type_ list ->
              (termnode Verifast0.chunk ->
               termnode Verifast0.chunk list ->
               termnode ->
               termnode list ->
               Verifast0.chunk_info option ->
               string list ->
               termnode Verifast0.env -> (string * termnode) list -> 'a) ->
              'a
            val consume_chunk :
              (termnode *
               (termnode Verifast0.heap ->
                Ast.type_ list ->
                bool ->
                termnode list -> (termnode Verifast0.heap option -> 'a) -> 'a)
               list)
              list ->
              termnode Verifast0.heap ->
              string list ->
              termnode Verifast0.env ->
              (string * termnode) list ->
              Lexer.loc ->
              termnode * bool ->
              Ast.type_ list ->
              termnode ->
              termnode Verifast0.pat0 ->
              int option ->
              termnode Verifast0.pat0 list ->
              (termnode Verifast0.chunk ->
               termnode Verifast0.chunk list ->
               termnode ->
               termnode list ->
               Verifast0.chunk_info option ->
               string list ->
               termnode Verifast0.env -> (string * termnode) list -> 'a) ->
              'a
            val srcpat : Ast.pat -> 'a Verifast0.pat0
            val srcpats : Ast.pat list -> 'a Verifast0.pat0 list
            val consume_asn_core :
              (termnode *
               (termnode Verifast0.heap ->
                Ast.type_ list ->
                bool ->
                termnode list ->
                (termnode Verifast0.heap option -> Verifast0.symexec_result) ->
                Verifast0.symexec_result)
               list)
              list ->
              (string * Ast.type_) list ->
              termnode Verifast0.heap ->
              string list ->
              termnode Verifast0.env ->
              (string * termnode) list ->
              Ast.asn ->
              bool ->
              termnode ->
              (termnode Verifast0.chunk list ->
               termnode Verifast0.heap ->
               string list ->
               termnode Verifast0.env ->
               (string * termnode) list ->
               Verifast0.chunk_info option -> Verifast0.symexec_result) ->
              Verifast0.symexec_result
            val consume_asn :
              (termnode *
               (termnode Verifast0.heap ->
                Ast.type_ list ->
                bool ->
                termnode list ->
                (termnode Verifast0.heap option -> Verifast0.symexec_result) ->
                Verifast0.symexec_result)
               list)
              list ->
              (string * Ast.type_) list ->
              termnode Verifast0.heap ->
              string list ->
              termnode Verifast0.env ->
              Ast.asn ->
              bool ->
              termnode ->
              (termnode Verifast0.chunk list ->
               termnode Verifast0.heap ->
               string list ->
               termnode Verifast0.env ->
               Verifast0.chunk_info option -> Verifast0.symexec_result) ->
              Verifast0.symexec_result
            val term_of_pred_index : string -> termnode
            val predinstmap_by_predfamsymb :
              (termnode * ((string * Ast.type_) list * Ast.asn)) list
            val empty_preds :
              (termnode * termnode list * Ast.expr list list *
               ((string * string list) *
                ((string * termnode) list * Lexer.loc * string list *
                 (string * Ast.type_) list * termnode * int option * 
                 Ast.asn)))
              list
            val pred_fam_contains_edges :
              (termnode * termnode list * termnode *
               (Lexer.loc * (termnode * bool) * bool * string list *
                string list * (string * Ast.type_) list *
                (string * Ast.type_) list * Ast.asn * Ast.pat option *
                Ast.expr option * Ast.type_ list * Ast.expr list *
                Ast.expr list * Ast.expr list)
               list)
              list
            val instance_predicate_contains_edges :
              (termnode * termnode list * termnode *
               (Lexer.loc * (termnode * bool) * bool * 'a list *
                string list * Ast.type_ map * 'b list * Ast.asn *
                Ast.pat option * Ast.expr option * Ast.type_ list *
                Ast.expr list * Ast.expr list * Ast.expr list)
               list)
              list
            val contains_edges :
              (termnode * termnode list * termnode *
               (Lexer.loc * (termnode * bool) * bool * string list *
                string list * Ast.type_ map * (string * Ast.type_) list *
                Ast.asn * Ast.pat option * Ast.expr option * Ast.type_ list *
                Ast.expr list * Ast.expr list * Ast.expr list)
               list)
              list
            val close1_ :
              ('a * 'b list * 'a *
               ('c * 'd * 'e * 'f * string list * 'g * 'h * 'i * 'j * 'k *
                'l * Ast.expr list * 'm * Ast.expr list)
               list)
              list ->
              ('a * 'b list * 'a *
               ('c * 'd * 'e * 'f * string list * 'g * 'h * 'i * 'j * 'k *
                'l * Ast.expr list * 'm * Ast.expr list)
               list)
              list
            val transitive_contains_edges_ :
              (termnode * termnode list * termnode *
               (Lexer.loc * (termnode * bool) * bool * string list *
                string list * Ast.type_ map * (string * Ast.type_) list *
                Ast.asn * Ast.pat option * Ast.expr option * Ast.type_ list *
                Ast.expr list * Ast.expr list * Ast.expr list)
               list)
              list
            val rules_cell :
              (termnode *
               (termnode Verifast0.heap ->
                Ast.type_ list ->
                bool ->
                termnode list ->
                (termnode Verifast0.heap option -> Verifast0.symexec_result) ->
                Verifast0.symexec_result)
               list)
              list ref
            val rules :
              (termnode *
               (termnode Verifast0.heap ->
                Ast.type_ list ->
                bool ->
                termnode list ->
                (termnode Verifast0.heap option -> Verifast0.symexec_result) ->
                Verifast0.symexec_result)
               list)
              list
          end
    end
