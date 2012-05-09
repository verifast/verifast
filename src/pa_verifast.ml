open Camlp4
open Sig

module Id = struct
  let name = "pa_verifast"
  let version = "0.1"
  let description = "some OCaml syntax extensions for the VeriFast codebase"
end

module Make (Syntax : Sig.Camlp4Syntax) = struct
  include Syntax

  EXTEND Gram
    GLOBAL: expr;
    
    expr: BEFORE "top"
      [ NONA
          [ "compute"; e = expr; bs = where_bindings -> bs e ] ];
    
    where_bindings:
      [ NONA
          [ "where"; OPT "let"; rf = opt_rec; lb = where_binding; bs = where_bindings -> (fun e -> bs <:expr< let $rec:rf$ $lb$ in $e$ >>)
            | "end" -> fun e -> e ] ];
    
    where_binding:
      [ LEFTA
          [ b1 = SELF; "and"; b2 = SELF -> <:binding< $b1$ and $b2$ >>
            | p = ipatt; e = fun_binding -> <:binding< $p$ = $e$ >> ] ];
    
    END
end

let module M = Register.OCamlSyntaxExtension(Id)(Make) in ()
