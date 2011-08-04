(* Source: Alain Frish <http://ocaml.janestreet.com/?q=node/18> *)

type dyn = bool -> unit

let create_ctor () =
  let r = ref None in
  let cons x = let sx = Some x in fun b -> r := if b then sx else None in
  let match_ d = d true; let v = !r in d false; v in
  cons, match_