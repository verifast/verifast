module type VERIFY_PROGRAM_ARGS =
  sig
    val emitter_callback : Ast.package list -> unit
    type typenode
    type symbol
    type termnode
    val ctxt : (typenode, symbol, termnode) Proverapi.context
    val options : Verifast0.options
    val program_path : string
    val reportRange : Lexer.range_kind -> Lexer.loc -> unit
    val reportUseSite : Lexer.decl_kind -> Lexer.loc -> Lexer.loc -> unit
    val breakpoint : (string * int) option
  end
module VerifyProgram1 :
  functor (VerifyProgramArgs : VERIFY_PROGRAM_ARGS) ->
    sig
      include VERIFY_PROGRAM_ARGS
      val path : string
      val language : Ast.language
      val initial_verbosity : int
      val disable_overflow_check : bool
      val allow_should_fail : bool
      val emit_manifest : bool
      val include_paths : string list
      val verbosity : int ref
      val set_verbosity : int -> unit
      val class_counter : int ref
      val used_ids : (string, int ref) Hashtbl.t
      val used_ids_undo_stack : int ref list ref
      val dummy_frac_terms : termnode list ref
      val used_ids_stack : (int ref list * termnode list) list ref
      val undoStack : (unit -> unit) list ref
      val push_undo_item : (unit -> unit) -> unit
      val undoStackStack : (unit -> unit) list list ref
      val push_undoStack : unit -> unit
      val pop_undoStack : unit -> unit
      val contextStack : termnode Verifast0.context list ref
      val push_context : termnode Verifast0.context -> unit
      val pop_context : unit -> unit
      val contextStackStack : termnode Verifast0.context list list ref
      val push_contextStack : unit -> unit
      val pop_contextStack : unit -> unit
      val with_context : termnode Verifast0.context -> (unit -> 'a) -> 'a
      val push : unit -> unit
      val pop : unit -> unit
      val in_temporary_context : (unit -> 'a) -> 'a
      val execute_branch : (unit -> Verifast0.symexec_result) -> unit
      val get_ident_use_count_cell : string -> int ref
      val mk_ident : string -> string
      val apply_conversion :
        Ast.prover_type -> Ast.prover_type -> termnode -> termnode
      val typenode_of_provertype : Ast.prover_type -> typenode
      val mk_symbol :
        string ->
        typenode list -> typenode -> Proverapi.symbol_kind -> symbol
      val apply_symbol : symbol
      val mk_func_symbol :
        string ->
        Ast.prover_type list ->
        Ast.prover_type -> Proverapi.symbol_kind -> symbol * termnode
      val mk_app : symbol * 'a -> termnode list -> termnode
      val provertype_of_type : Ast.type_ -> Ast.prover_type
      val typenode_of_type : Ast.type_ -> typenode
      val get_class_symbol : symbol
      val class_serial_number : symbol
      val bitwise_or_symbol : symbol
      val bitwise_xor_symbol : symbol
      val bitwise_and_symbol : symbol
      val bitwise_not_symbol : symbol
      val arraylength_symbol : symbol
      val shiftleft_int32_symbol : symbol
      val shiftright_symbol : symbol
      val truncate_int8_symbol : symbol
      val truncate_int16_symbol : symbol
      val boolt : Ast.type_
      val intt : Ast.type_
      val instanceof_symbol : symbol
      val array_type_symbol : symbol
      val two_big_int : Big_int.big_int
      val real_zero : termnode
      val real_unit : termnode
      val real_half : termnode
      val int_zero_term : termnode
      val min_uint_term : termnode
      val max_uint_term : termnode
      val min_ptr_big_int : Big_int.big_int
      val max_ptr_big_int : Big_int.big_int
      val max_ptr_term : termnode
      val min_int_big_int : Big_int.big_int
      val min_int_term : termnode
      val max_int_big_int : Big_int.big_int
      val max_int_term : termnode
      val min_ushort_big_int : Big_int.big_int
      val min_ushort_term : termnode
      val max_ushort_big_int : Big_int.big_int
      val max_ushort_term : termnode
      val min_short_big_int : Big_int.big_int
      val min_short_term : termnode
      val max_short_big_int : Big_int.big_int
      val max_short_term : termnode
      val min_uchar_big_int : Big_int.big_int
      val min_uchar_term : termnode
      val max_uchar_big_int : Big_int.big_int
      val max_uchar_term : termnode
      val min_char_big_int : Big_int.big_int
      val min_char_term : termnode
      val max_char_big_int : Big_int.big_int
      val max_char_term : termnode
      val get_unique_var_symb : string -> Ast.type_ -> termnode
      val assume_bounds : termnode -> Ast.type_ -> unit
      val get_unique_var_symb_non_ghost : string -> Ast.type_ -> termnode
      val get_unique_var_symb_ : string -> Ast.type_ -> bool -> termnode
      val get_dummy_frac_term : unit -> termnode
      val is_dummy_frac_term : termnode -> bool
      val get_unique_var_symbs_ :
        (string * Ast.type_) list -> bool -> (string * termnode) list
      val get_unique_var_symbs_non_ghost :
        (string * Ast.type_) list -> (string * termnode) list
      val real_unit_pat : termnode Verifast0.pat0
      val plugin_context :
        < assert_formula : termnode -> Plugins.rel -> termnode -> bool;
          mk_symbol : string -> Plugins.term_type -> termnode; pop : 
          unit; push : unit;
          query_formula : termnode -> Plugins.rel -> termnode -> bool >
      val current_module_name : string
      val current_module_term : termnode
      val modulemap : (string * termnode) list
      val programDir : string
      val rtpath : string
      val shouldFailLocs : Lexer.loc list ref
      val reportShouldFail : Lexer.loc -> unit
      val check_should_fail : 'a -> (unit -> 'a) -> 'a
      val prototypes_used : (string * Lexer.loc) list ref
      val register_prototype_used : Lexer.loc -> string -> unit
      val extract_specs : Ast.package list -> Ast.decl list * Ast.decl list
      module CheckFileTypes :
        sig
          type 'a map = (string * 'a) list
          type struct_field_info = Lexer.loc * Ast.ghostness * Ast.type_
          type struct_info =
              Lexer.loc * (string * struct_field_info) list option *
              termnode option
          type enum_info = Big_int.big_int
          type global_info =
              Lexer.loc * Ast.type_ * termnode * Ast.expr option ref
          type func_symbol = symbol * termnode
          type pure_func_info =
              Lexer.loc * string list * Ast.type_ * Ast.type_ list *
              func_symbol
          type inductive_ctor_info = string * pure_func_info
          type inductive_info =
              Lexer.loc * string list * (string * inductive_ctor_info) list *
              string list option
          type pred_ctor_info =
              PredCtorInfo of Lexer.loc * (string * Ast.type_) list *
                (string * Ast.type_) list * Ast.asn * func_symbol
          type pred_fam_info =
              Lexer.loc * string list * int * Ast.type_ list * termnode *
              int option
          type malloc_block_pred_info = string * pred_fam_info
          type field_pred_info = string * pred_fam_info
          type pred_inst_info =
              (string * termnode) list * Lexer.loc * string list *
              (string * Ast.type_) list * termnode * int option * Ast.asn
          type pred_inst_map = ((string * string list) * pred_inst_info) list
          type func_info =
              FuncInfo of (string * termnode) list * termnode option *
                Lexer.loc * Ast.func_kind * string list * Ast.type_ option *
                (string * Ast.type_) list * bool * Ast.asn *
                (string * Ast.type_) list * Ast.asn *
                (string * pred_fam_info map * Ast.type_ list *
                 (Lexer.loc * string) list)
                option * (Ast.stmt list * Lexer.loc) option option *
                Ast.method_binding * Ast.visibility
          type func_type_info =
              Lexer.loc * Ast.ghostness * string list * Ast.type_ option *
              Ast.type_ map * Ast.type_ map * Ast.asn * Ast.asn *
              pred_fam_info map
          type signature = string * Ast.type_ list
          type method_info =
              Lexer.loc * Ast.ghostness * Ast.type_ option * Ast.type_ map *
              Ast.asn * Ast.type_ map * Ast.asn *
              (Ast.type_ * Ast.asn) list * Ast.asn * Ast.asn *
              (Ast.type_ * Ast.asn) list *
              (Ast.stmt list * Lexer.loc) option option *
              Ast.method_binding * Ast.visibility * bool * bool
          type interface_method_info =
              Lexer.loc * Ast.ghostness * Ast.type_ option * Ast.type_ map *
              Ast.asn * Ast.type_ map * Ast.asn *
              (Ast.type_ * Ast.asn) list * Ast.visibility * bool
          type field_info = {
            fl : Lexer.loc;
            fgh : Ast.ghostness;
            ft : Ast.type_;
            fvis : Ast.visibility;
            fbinding : Ast.method_binding;
            ffinal : bool;
            finit : Ast.expr option;
            fvalue : Ast.constant_value option option ref;
          }
          type ctor_info =
              Lexer.loc * Ast.type_ map * Ast.asn * Ast.type_ map * Ast.asn *
              (Ast.type_ * Ast.asn) list *
              (Ast.stmt list * Lexer.loc) option option * Ast.visibility
          type inst_pred_info =
              Lexer.loc * Ast.type_ map * string * termnode * Ast.asn option
          type interface_inst_pred_info =
              Lexer.loc * Ast.type_ map * string * termnode
          type interface_info =
              InterfaceInfo of Lexer.loc * field_info map *
                (signature * interface_method_info) list *
                interface_inst_pred_info map * string list
          type class_info = {
            cl : Lexer.loc;
            cabstract : bool;
            cfinal : Ast.class_finality;
            cmeths : (signature * method_info) list;
            cfds : field_info map;
            cctors : (Ast.type_ list * ctor_info) list;
            csuper : string;
            cinterfs : string list;
            cpreds : inst_pred_info map;
            cpn : string;
            cilist : Ast.import list;
          }
          type plugin_info =
              (Plugins.plugin * termnode Plugins.plugin_instance) * termnode
          type box_action_info =
              Lexer.loc * Ast.type_ map * Ast.expr * Ast.expr
          type box_handle_predicate_info =
              Lexer.loc * Ast.type_ map * Ast.expr *
              Ast.preserved_by_clause list
          type box_info =
              Lexer.loc * Ast.type_ map * Ast.asn * Ast.type_ map *
              box_action_info map * box_handle_predicate_info map
          type maps =
              struct_info map * enum_info map * global_info map *
              inductive_info map * pure_func_info map * pred_ctor_info map *
              malloc_block_pred_info map *
              ((string * string) * field_pred_info) list *
              pred_fam_info map * pred_inst_map * Ast.type_ map *
              func_type_info map * func_info map * box_info map *
              class_info map * interface_info map * termnode map *
              termnode map * plugin_info map
          type implemented_prototype_info = string * Lexer.loc
          type implemented_function_type_info =
              string * Lexer.loc * string * string list * bool
          type check_file_output =
              implemented_prototype_info list *
              implemented_function_type_info list
        end
      include module type of CheckFileTypes
      val headermap : ((Lexer.loc * string) list * maps) map ref
      val spec_classes : Ast.decl list ref
      val spec_lemmas : Ast.decl list ref
      module type CHECK_FILE_ARGS =
        sig
          val filepath : string
          val is_import_spec : bool
          val include_prelude : bool
          val basedir : string
          val reldir : string
          val headers : (Lexer.loc * string) list
          val ps : Ast.package list
          val check_file :
            string ->
            bool ->
            bool ->
            string ->
            string ->
            (Lexer.loc * string) list ->
            Ast.package list -> check_file_output * maps
        end
      module CheckFile1 :
        functor (CheckFileArgs : CHECK_FILE_ARGS) ->
          sig
            include CHECK_FILE_ARGS
            val is_jarspec : bool
            val structmap0 : struct_info map
            val enummap0 : enum_info map
            val globalmap0 : global_info map
            val inductivemap0 : inductive_info map
            val purefuncmap0 : pure_func_info map
            val predctormap0 : pred_ctor_info map
            val malloc_block_pred_map0 : malloc_block_pred_info map
            val field_pred_map0 : ((string * string) * field_pred_info) list
            val predfammap0 : pred_fam_info map
            val predinstmap0 : pred_inst_map
            val typedefmap0 : Ast.type_ map
            val functypemap0 : func_type_info map
            val funcmap0 : func_info map
            val boxmap0 : box_info map
            val classmap0 : class_info map
            val interfmap0 : interface_info map
            val classterms0 : termnode map
            val interfaceterms0 : termnode map
            val pluginmap0 : plugin_info map
            val pluginmap1 :
              (string *
               ((Plugins.plugin * termnode Plugins.plugin_instance) *
                termnode))
              list
            val pluginmap : (string * plugin_info) list
            val unloadable : bool
            val typedefdeclmap : (string * (Lexer.loc * Ast.type_expr)) list
            val structdeclmap :
              (string * (Lexer.loc * Ast.field list option)) list
            val enumdeclmap :
              (string * (Lexer.loc * (string * Ast.expr option) list)) list
            val enummap1 : (string * enum_info) list
            val functypenames :
              (string *
               (Lexer.loc * Ast.ghostness * string list *
                (Ast.type_expr * string) list))
              list
            val inductivedeclmap :
              (string * (Lexer.loc * string list * Ast.ctor list)) list
            val try_assoc' :
              string * Ast.import list ->
              string -> (string * 'a) list -> 'a option
            val try_assoc_pair' :
              string * Ast.import list ->
              string * string list ->
              ((string * string list) * 'a) list -> 'a option
            val try_assoc2' :
              string * Ast.import list ->
              string -> (string * 'a) list -> (string * 'a) list -> 'a option
            val search :
              string ->
              string * Ast.import list -> (string * 'a) list -> bool
            val search' :
              string ->
              string * Ast.import list -> (string * 'a) list -> string option
            val resolve :
              string * Ast.import list ->
              Lexer.loc ->
              string -> (string * 'a) list -> (string * 'a) option
            val search2' :
              string ->
              string * Ast.import list ->
              (string * 'a) list -> (string * 'b) list -> string option
            val inductive_arities : (string * (Lexer.loc * int)) list
            val check_pure_type_core :
              (string * Ast.type_) list ->
              string * Ast.import list ->
              string list -> Ast.type_expr -> Ast.type_
            val typedefmap1 : (string * Ast.type_) list
            val typedefmap : (string * Ast.type_) list
            val check_pure_type :
              string * Ast.import list ->
              string list -> Ast.type_expr -> Ast.type_
            val instantiate_type :
              (string * Ast.type_) list -> Ast.type_ -> Ast.type_
            val instantiate_types :
              (string * Ast.type_) list -> Ast.type_ list -> Ast.type_ list
            val terms_of : (string * 'a) list -> (string * termnode) list
            val classterms1 : (string * termnode) list
            val interfaceterms1 : (string * termnode) list
            val classterms : (string * termnode) list
            val interfaceterms : (string * termnode) list
            val structmap1 :
              (string *
               (Lexer.loc *
                (string * (Lexer.loc * Ast.ghostness * Ast.type_)) list
                option * termnode option))
              list
            val structmap : (string * struct_info) list
            val enummap : (string * enum_info) list
            val isfuncs :
              (string *
               ((((string * string) * int * int) *
                 ((string * string) * int * int)) *
                'a list * Ast.type_ * Ast.type_ list * (symbol * termnode)))
              list
            val is_subtype_of : string -> string -> bool
            val is_subtype_of_ : Ast.type_ -> Ast.type_ -> bool
            val is_unchecked_exception_type : Ast.type_ -> bool
            val globaldeclmap :
              (string *
               (Lexer.loc * Ast.type_ * termnode * Ast.expr option ref))
              list
            val globalmap1 :
              (string *
               (Lexer.loc * Ast.type_ * termnode * Ast.expr option ref))
              list
            val globalmap : (string * global_info) list
            val compatible_pointees : Ast.type_ -> Ast.type_ -> bool
            val unfold_inferred_type : Ast.type_ -> Ast.type_
            val unify : Ast.type_ -> Ast.type_ -> bool
            val expect_type_core :
              Lexer.loc -> string -> Ast.type_ -> Ast.type_ -> unit
            val expect_type : Lexer.loc -> Ast.type_ -> Ast.type_ -> unit
            val is_assignable_to : Ast.type_ -> Ast.type_ -> bool
            val is_assignable_to_sign :
              Ast.type_ list -> Ast.type_ list -> bool
            val convert_provertype_expr :
              Ast.expr -> Ast.prover_type -> Ast.prover_type -> Ast.expr
            val box : Ast.expr -> Ast.type_ -> Ast.type_ -> Ast.expr
            val unbox : Ast.expr -> Ast.type_ -> Ast.type_ -> Ast.expr
            val check_tparams :
              Lexer.loc -> string list -> string list -> unit
            val inductivemap1 :
              (string *
               (Lexer.loc * string list *
                (string *
                 (string *
                  (Lexer.loc * string list * Ast.type_ * Ast.type_ list *
                   (symbol * termnode))))
                list * string list option))
              list
            val inductivemap : (string * inductive_info) list
            val is_universal_type : Ast.type_ -> bool
            val mk_predfam :
              string ->
              'a ->
              string list ->
              'b ->
              Ast.type_ list ->
              int option ->
              string *
              ('a * string list * 'b * Ast.type_ list * termnode * int option)
            val struct_padding_predfams1 :
              (string *
               (Lexer.loc * 'a list * int * Ast.type_ list * termnode *
                int option))
              list
            val functypedeclmap1 :
              (string *
               (Lexer.loc * Ast.ghostness * string list * Ast.type_ option *
                (string * Ast.type_) list * (string * Ast.type_) list *
                string * Ast.import list * Ast.asn * Ast.asn *
                (string *
                 (Lexer.loc * string list * int * Ast.type_ list * termnode *
                  int option))
                list))
              list
            val isparamizedfunctypepreds1 :
              (string *
               (Lexer.loc * string list * int * Ast.type_ list * termnode *
                int option))
              list
            val malloc_block_pred_map1 :
              (string *
               (string *
                (Lexer.loc * string list * int * Ast.type_ list * termnode *
                 int option)))
              list
            val malloc_block_pred_map :
              (string * malloc_block_pred_info) list
            val field_pred_map1 :
              ((string * string) *
               (string *
                (Lexer.loc * string list * int * Ast.type_ list * termnode *
                 int option)))
              list
            val field_pred_map : ((string * string) * field_pred_info) list
            val structpreds1 :
              (string *
               (Lexer.loc * string list * int * Ast.type_ list * termnode *
                int option))
              list
            val predfammap1 : (string * pred_fam_info) list
            val predfammap : (string * pred_fam_info) list
            val purefuncmap1 : (string * pure_func_info) list
            val purefuncmap : (string * pure_func_info) list
            val funcnames : string list
            val check_classname :
              string * Ast.import list -> Lexer.loc * string -> string
            val check_classnamelist :
              string * Ast.import list ->
              (Lexer.loc * string) list -> string list
            val check_funcnamelist : (Lexer.loc * string) list -> string list
            val interfmap1 :
              (string *
               (Lexer.loc * (string * field_info) list * Ast.meth list *
                (string * (Lexer.loc * Ast.type_ map * string * termnode))
                list * string list * string * Ast.import list))
              list
            val lookup_class_field :
              string -> string -> (field_info * string) option
            val is_package : string -> bool
            val current_class : string
            val check_expr_t_core :
              (string *
               ('a * 'b * 'c * Ast.type_ option * 'd * 'e * 'f * 'g * 'h))
              list ->
              (string * func_info) list ->
              (string * class_info) list ->
              (string * interface_info) list ->
              string * Ast.import list ->
              string list ->
              (string * Ast.type_) list -> Ast.expr -> Ast.type_ -> Ast.expr
            val check_expr_t_core_core :
              (string *
               ('a * 'b * 'c * Ast.type_ option * 'd * 'e * 'f * 'g * 'h))
              list ->
              (string * func_info) list ->
              (string * class_info) list ->
              (string * interface_info) list ->
              string * Ast.import list ->
              string list ->
              (string * Ast.type_) list ->
              Ast.expr -> Ast.type_ -> bool -> Ast.expr
            val check_deref_core :
              (string *
               ('a * 'b * 'c * Ast.type_ option * 'd * 'e * 'f * 'g * 'h))
              list ->
              (string * func_info) list ->
              (string * class_info) list ->
              (string * interface_info) list ->
              string * Ast.import list ->
              Lexer.loc ->
              string list ->
              (string * Ast.type_) list ->
              Ast.expr ->
              string -> Ast.expr * Ast.type_ * Big_int.big_int option
            val check_expr_core :
              (string *
               ('a * 'b * 'c * Ast.type_ option * 'd * 'e * 'f * 'g * 'h))
              list ->
              (string * func_info) list ->
              (string * class_info) list ->
              (string * interface_info) list ->
              string * Ast.import list ->
              string list ->
              (string * Ast.type_) list -> Ast.expr -> Ast.expr * Ast.type_
            val check_expr :
              string * Ast.import list ->
              string list ->
              (string * Ast.type_) list -> Ast.expr -> Ast.expr * Ast.type_
            val check_expr_t :
              string * Ast.import list ->
              string list ->
              (string * Ast.type_) list -> Ast.expr -> Ast.type_ -> Ast.expr
            val fixpointmap1 :
              (string *
               (Lexer.loc * Ast.type_ * (string * Ast.type_) list *
                int option * Ast.expr * string * Ast.import list * symbol))
              list
            val check_static_field_initializer : Ast.expr -> unit
            val check_c_initializer : Ast.expr -> Ast.type_ -> Ast.expr
            val merge_tenvs :
              Lexer.loc ->
              (string * 'a) list -> (string * 'a) list -> (string * 'a) list
            val check_pat_core :
              string * Ast.import list ->
              string list ->
              (string * Ast.type_) list ->
              Ast.type_ -> Ast.pat -> Ast.pat * (string * Ast.type_) list
            val check_pats_core :
              string * Ast.import list ->
              Lexer.loc ->
              string list ->
              (string * Ast.type_) list ->
              Ast.type_ list ->
              Ast.pat list -> Ast.pat list * (string * Ast.type_) list
            val check_pat :
              string * Ast.import list ->
              string list ->
              (string * Ast.type_) list ->
              Ast.type_ -> Ast.pat -> Ast.pat * (string * Ast.type_) list
            val check_pats :
              string * Ast.import list ->
              Lexer.loc ->
              string list ->
              (string * Ast.type_) list ->
              Ast.type_ list ->
              Ast.pat list -> Ast.pat list * (string * Ast.type_) list
            val get_class_of_this : Ast.expr
            val get_class_finality : string -> Ast.class_finality
            val check_inst_pred_asn :
              Lexer.loc ->
              string ->
              string -> (string -> Ast.type_ map -> 'a) -> (unit -> 'a) -> 'a
            val check_asn_core :
              string * Ast.import list ->
              string list ->
              (string * Ast.type_) list ->
              Ast.asn ->
              Ast.asn * (string * Ast.type_) list * Ast.type_ option ref list
            val fix_inferred_type : Ast.type_ option ref -> unit
            val fix_inferred_types : Ast.type_ option ref list -> unit
            val check_asn :
              string * Ast.import list ->
              string list ->
              (string * Ast.type_) list ->
              Ast.asn -> Ast.asn * (string * Ast.type_) list
            val boxmap :
              (string *
               (Lexer.loc * (string * Ast.type_) list * Ast.asn *
                (string * Ast.type_) list *
                (string *
                 (Lexer.loc * (string * Ast.type_) list * Ast.expr * Ast.expr))
                list *
                (string *
                 (Lexer.loc * (string * Ast.type_) list * Ast.expr *
                  Ast.preserved_by_clause list))
                list))
              list
            val vars_used : Ast.expr -> string list
            val assert_expr_fixed : string list -> Ast.expr -> unit
            val fixed_pat_fixed_vars : Ast.pat -> string list
            val assume_pat_fixed : string list -> Ast.pat -> string list
            val assert_pats_fixed :
              Lexer.loc -> string list -> Ast.pat list -> unit
            val assume_pats_fixed :
              string list -> Ast.pat list -> string list
            val expr_is_fixed : string list -> Ast.expr -> bool
            val check_pred_precise : string list -> Ast.asn -> string list
            val check_predinst0 :
              string list ->
              int ->
              Ast.type_ list ->
              'a ->
              int option ->
              string * Ast.import list ->
              string list ->
              (string * Ast.type_) list ->
              'b ->
              Lexer.loc ->
              'c ->
              string list ->
              'd list ->
              (Ast.type_expr * string) list ->
              Ast.asn ->
              ('c * 'd list) *
              ('b * Lexer.loc * string list * (string * Ast.type_) list *
               'a * int option * Ast.asn)
            val check_predinst :
              string * Ast.import list ->
              string list ->
              (string * Ast.type_) list ->
              'a ->
              Lexer.loc ->
              string ->
              string list ->
              'b list ->
              (Ast.type_expr * string) list ->
              Ast.asn ->
              (string * 'b list) *
              ('a * Lexer.loc * string list * (string * Ast.type_) list *
               termnode * int option * Ast.asn)
            val predinstmap1 :
              ((string * string list) *
               ('a list * Lexer.loc * string list *
                (string * Ast.type_) list * termnode * int option * Ast.asn))
              list
            val predinstmap : ((string * string list) * pred_inst_info) list
            val predctormap1 : (string * pred_ctor_info) list
            val predctormap : (string * pred_ctor_info) list
            val classmap1 :
              (string *
               (Lexer.loc * bool * Ast.class_finality * Ast.meth list *
                (string * field_info) list * Ast.cons list * string *
                string list *
                (string *
                 (Lexer.loc * Ast.type_ map * string * termnode *
                  Ast.asn option))
                list * string * Ast.import list))
              list
            val check_ghost : string list -> 'a -> Ast.expr -> unit
            val funcnameterms : (string * termnode) list
            val struct_sizes : (string * termnode) list
            val sizeof : Lexer.loc -> Ast.type_ -> termnode
            val field_offsets : ((string * string) * termnode) list
            val field_offset : Lexer.loc -> string -> string -> termnode
            val field_address :
              Lexer.loc -> termnode -> string -> string -> termnode
            val convert_provertype :
              termnode -> Ast.prover_type -> Ast.prover_type -> termnode
            val prover_convert_term :
              termnode -> Ast.type_ -> Ast.type_ -> termnode
            val get_pred_symb : string -> termnode
            val lazy_value : (unit -> 'a) -> unit -> 'a
            val lazy_predfamsymb : string -> unit -> termnode
            val array_element_symb : unit -> termnode
            val array_slice_symb : unit -> termnode
            val array_slice_deep_symb : unit -> termnode
            val mk_nil : unit -> termnode
            val mk_cons : Ast.type_ -> termnode -> termnode -> termnode
            val mk_all_eq : Ast.type_ -> termnode -> termnode -> termnode
            val mk_list : Ast.type_ -> termnode list -> termnode
            val mk_take : termnode -> termnode -> termnode
            val mk_drop : termnode -> termnode -> termnode
            val mk_append : termnode -> termnode -> termnode
            val mk_length : termnode -> termnode
            val mk_zero_list : int -> termnode
            val mk_char_list_of_c_string : int -> string -> termnode
            val assume :
              termnode ->
              (unit -> Verifast0.symexec_result) -> Verifast0.symexec_result
            val assume_eq :
              termnode ->
              termnode ->
              (unit -> Verifast0.symexec_result) -> Verifast0.symexec_result
            val assume_neq :
              termnode ->
              termnode ->
              (unit -> Verifast0.symexec_result) -> Verifast0.symexec_result
            val pprint_context_term : termnode -> string
            val pprint_context_stack :
              termnode Verifast0.context list ->
              string Verifast0.context list
            val assert_term :
              termnode ->
              'a -> 'b -> Lexer.loc -> string -> string option -> unit
            val assert_false :
              'a -> 'b -> Lexer.loc -> string -> string option -> 'c
            val prover_type_term : Lexer.loc -> Ast.type_ -> termnode
            val eval_op :
              Lexer.loc ->
              Ast.operator ->
              termnode ->
              termnode ->
              Ast.type_ list option ->
              (Lexer.loc -> termnode -> string -> string option -> unit)
              option -> termnode
            val eval_core_cps0 :
              ('a option ->
               'b option -> (string * termnode) list -> Ast.expr -> termnode) ->
              ('c -> Ast.expr -> ('c -> termnode -> 'd) -> 'd) ->
              'c ->
              (Lexer.loc -> termnode -> string -> string option -> unit)
              option ->
              ((Lexer.loc -> termnode -> string -> string -> termnode) *
               (Lexer.loc -> string -> string -> termnode) *
               (Lexer.loc -> termnode -> Ast.type_ -> termnode) *
               (Lexer.loc -> termnode -> termnode -> Ast.type_ -> termnode))
              option ->
              (string * termnode) list ->
              Ast.expr -> ('c -> termnode -> 'd) -> 'd
            val eval_core :
              (Lexer.loc -> termnode -> string -> string option -> unit)
              option ->
              ((Lexer.loc -> termnode -> string -> string -> termnode) *
               (Lexer.loc -> string -> string -> termnode) *
               (Lexer.loc -> termnode -> Ast.type_ -> termnode) *
               (Lexer.loc -> termnode -> termnode -> Ast.type_ -> termnode))
              option -> (string * termnode) list -> Ast.expr -> termnode
            val eval_core_cps :
              ('a -> Ast.expr -> ('a -> termnode -> 'b) -> 'b) ->
              'a ->
              (Lexer.loc -> termnode -> string -> string option -> unit)
              option ->
              ((Lexer.loc -> termnode -> string -> string -> termnode) *
               (Lexer.loc -> string -> string -> termnode) *
               (Lexer.loc -> termnode -> Ast.type_ -> termnode) *
               (Lexer.loc -> termnode -> termnode -> Ast.type_ -> termnode))
              option ->
              (string * termnode) list ->
              Ast.expr -> ('a -> termnode -> 'b) -> 'b
            val eval :
              ((Lexer.loc -> termnode -> string -> string -> termnode) *
               (Lexer.loc -> string -> string -> termnode) *
               (Lexer.loc -> termnode -> Ast.type_ -> termnode) *
               (Lexer.loc -> termnode -> termnode -> Ast.type_ -> termnode))
              option -> (string * termnode) list -> Ast.expr -> termnode
          end
    end
