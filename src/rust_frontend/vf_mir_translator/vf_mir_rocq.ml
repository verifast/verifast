open Rocq_writer
module D = Vf_mir_decoder

let rocq_print_u128 writer (n: D.uint128) =
  let v = Decoder_aux.uint128_get n in
  rocq_print_N writer (Stdint.Uint128.to_string v)

let rec rocq_print_ty writer ({kind}: D.ty) =
  match kind with
  | D.Bool ->
      rocq_print_ident writer "Bool"
  | D.UInt size ->
      rocq_print_application writer "Uint" @@ fun () ->
        rocq_print_argument writer @@ fun () ->
          begin match size with
          | D.U8 -> rocq_print_ident writer "U8"
          | D.U16 -> rocq_print_ident writer "U16"
          | D.U32 -> rocq_print_ident writer "U32"
          | D.U64 -> rocq_print_ident writer "U64"
          | D.U128 -> rocq_print_ident writer "U128"
          | D.USize -> rocq_print_ident writer "Usize"
          end
  | D.RawPtr {ty} ->
      rocq_print_application writer "RawPtr" @@ fun () ->
        rocq_print_argument writer @@ fun () ->
          rocq_print_ty writer ty
  | D.FnDef {id={name}; substs} ->
      rocq_print_application writer "FnDef" @@ fun () ->
        rocq_print_argument writer begin fun () ->
          rocq_print_string_literal writer name
        end;
        rocq_print_argument writer @@ fun () ->
          rocq_print_small_list writer @@ fun () ->
            substs |> List.iter @@ fun subst_ty ->
              rocq_print_small_list_element writer @@ fun () ->
                rocq_print_generic_arg writer subst_ty
  | D.Never ->
      rocq_print_ident writer "Never"
  | D.Tuple [] ->
      rocq_print_ident writer "Tuple0"
  | _ -> 
      rocq_print_ident writer "UnsupportedTy"
and rocq_print_generic_arg writer ({kind=arg}: D.generic_arg) =
  match arg with
  | D.Type ty ->
      rocq_print_application writer "Type_" @@ fun () ->
        rocq_print_argument writer @@ fun () ->
          rocq_print_ty writer ty
  | _ ->
      rocq_print_ident writer "UnsupportedGenArg"