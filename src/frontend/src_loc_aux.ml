open Ocaml_aux
open Ast

let is_well_formed_src_pos (path, ln, col) =
  if ln < 1 then
    Error (`IsWellFormedSrcPos ("Invalid line number: " ^ Int.to_string ln))
  else if col < 1 then
    Error (`IsWellFormedSrcPos ("Invalid column number: " ^ Int.to_string col))
  else Ok ()

let is_well_formed_loc0
    ((((spath, sln, scol) as spos), ((epath, eln, ecol) as epos)) : loc0) =
  let* _ = is_well_formed_src_pos spos in
  let* _ = is_well_formed_src_pos epos in
  if spath <> epath then
    Error
      (`IsWellFormedLoc0 "The start and end positions are not in the same file")
  else if not (sln < eln || (sln = eln && scol <= ecol)) then
    Error (`IsWellFormedLoc0 "The start and end positions are not in order")
  else Ok ()

let get_start_loc (loc : loc) =
  let loc0 = lexed_loc loc in
  let* _ = is_well_formed_loc0 loc0 in
  let spos, _ = loc0 in
  Ok (Lexed (spos, spos))

let get_last_col_loc (loc : loc) =
  let loc0 = lexed_loc loc in
  let* _ = is_well_formed_loc0 loc0 in
  let _, ((path, ln, col) as epos) = loc0 in
  if col > 1 (*1 based*) then Ok (Lexed ((path, ln, col - 1), epos))
  else Error (`GetLastColLoc "There is no column before end position column")

let try_compare_src_pos ((path1, ln1, col1) as pos1)
    ((path2, ln2, col2) as pos2) =
  let* _ = is_well_formed_src_pos pos1 in
  let* _ = is_well_formed_src_pos pos2 in
  if path1 <> path2 then
    Error
      (`TryCompareSrcPos "Cannot compare source positions in different files")
  else if ln1 > ln2 then Ok 1
  else if ln1 < ln2 then Ok (-1)
  else if col1 > col2 then Ok 1
  else if col1 < col2 then Ok (-1)
  else Ok 0

let cover_loc0 ((s1, e1) as l1 : loc0) ((s2, e2) as l2 : loc0) =
  let* _ = is_well_formed_loc0 l1 in
  let* _ = is_well_formed_loc0 l2 in
  let* scmp = try_compare_src_pos s1 s2 in
  let* ecmp = try_compare_src_pos e1 e2 in
  let s = if scmp < 0 then s1 else s2 in
  let e = if ecmp > 0 then e1 else e2 in
  Ok (s, e)

type inc_kind = LeftInRight | RightInLeft

type overlapping_kind =
  | Partial of { intersection : loc0; union : loc0 }
  | Inclusion of { kind : inc_kind }
  | Eq

type rel =
  | None
  | Disjoint of { compare : int }
  | Overlapping of { kind : overlapping_kind }

let rel l1 l2 =
  let* _ = is_well_formed_loc0 l1 in
  let* _ = is_well_formed_loc0 l2 in
  let (((spath1, _, _) as spos1), epos1), (((spath2, _, _) as spos2), epos2) =
    (l1, l2)
  in
  if spath1 <> spath2 then Ok None
  else
    let* cmp_s2_s1 = try_compare_src_pos spos2 spos1 in
    let s2_gt_s1 = cmp_s2_s1 > 0 in
    let* cmp_s2_e1 = try_compare_src_pos spos2 epos1 in
    let s2_lt_e1 = cmp_s2_e1 < 0 in
    let* cmp_e2_s1 = try_compare_src_pos epos2 spos1 in
    let e2_gt_s1 = cmp_e2_s1 > 0 in
    let* cmp_e2_e1 = try_compare_src_pos epos2 epos1 in
    let e2_lt_e1 = cmp_e2_e1 < 0 in
    let s2_eq_s1 = cmp_s2_s1 = 0 in
    let e2_eq_e1 = cmp_e2_e1 = 0 in
    match (s2_gt_s1, s2_lt_e1, e2_gt_s1, e2_lt_e1) with
    | true (*s2>s1*), true (*s2<e1*), true (*e2>s1*), true (*e2<e1*) ->
        Ok (Overlapping { kind = Inclusion { kind = RightInLeft } })
    | true (*s2>s1*), true (*s2<e1*), true (*e2>s1*), false (*e2>=e1*) ->
        Ok
          (Overlapping
             {
               kind =
                 Partial
                   { intersection = (spos2, epos1); union = (spos1, epos2) };
             })
    | true (*s2>s1*), true (*s2<e1*), false (*e2<=s1*), true (*e2<e1*) ->
        failwith "bug!" (*e2<s2*)
    | true (*s2>s1*), true (*s2<e1*), false (*e2<=s1*), false (*e2>=e1*) ->
        failwith "bug!" (*e2<s2*)
    | true (*s2>s1*), false (*s2>=e1*), true (*e2>s1*), true (*e2<e1*) ->
        failwith "bug!" (*e2<s2*)
    | true (*s2>s1*), false (*s2>=e1*), true (*e2>s1*), false (*e2>=e1*) ->
        Ok (Disjoint { compare = -1 })
    | true (*s2>s1*), false (*s2>=e1*), false (*e2<=s1*), true (*e2<e1*) ->
        failwith "bug!" (*e2<s2*)
    | true (*s2>s1*), false (*s2>=e1*), false (*e2<=s1*), false (*e2>=e1*) ->
        failwith "bug!" (*e2<s2*)
    | false (*s2<=s1*), true (*s2<e1*), true (*e2>s1*), true (*e2<e1*) ->
        Ok
          (Overlapping
             {
               kind =
                 Partial
                   { intersection = (spos1, epos2); union = (spos2, epos1) };
             })
    | false (*s2<=s1*), true (*s2<e1*), true (*e2>s1*), false (*e2>=e1*) ->
        if s2_eq_s1 && e2_eq_e1 then Ok (Overlapping { kind = Eq })
        else Ok (Overlapping { kind = Inclusion { kind = LeftInRight } })
    | false (*s2<=s1*), true (*s2<e1*), false (*e2<=s1*), true (*e2<e1*) ->
        Ok (Disjoint { compare = 1 })
    | false (*s2<=s1*), true (*s2<e1*), false (*e2<=s1*), false (*e2>=e1*) ->
        Ok (Disjoint { compare = 1 }) (*s1=e1=e2*)
    | false (*s2<=s1*), false (*s2>=e1*), true (*e2>s1*), true (*e2<e1*) ->
        failwith "bug!" (*s1=e1=s2 => no e2*)
    | false (*s2<=s1*), false (*s2>=e1*), true (*e2>s1*), false (*e2>=e1*) ->
        Ok (Disjoint { compare = -1 }) (*s1=e1=s2*)
    | false (*s2<=s1*), false (*s2>=e1*), false (*e2<=s1*), true (*e2<e1*) ->
        failwith "bug!" (*s1=e1=s2 => e2<s2*)
    | false (*s2<=s1*), false (*s2>=e1*), false (*e2<=s1*), false (*e2>=e1*) ->
        Ok (Overlapping { kind = Eq })
(*s1=e1=s2=e2*)

let try_compare_loc l1 l2 =
  let* rel = rel l1 l2 in
  match rel with
  | Disjoint { compare } -> Ok compare
  | None ->
      Error (`TryCompareLoc "Cannot compare source spans in different files")
  | Overlapping { kind = _ } ->
      print_endline (string_of_loc0 l1 ^ string_of_loc0 l2);
      Error (`TryCompareLoc "Not strictly ordered locations")

let compare_err_desc ei =
  match ei with
  | `IsWellFormedLoc0 msg -> "Malformed source span: " ^ msg
  | `IsWellFormedSrcPos msg -> "Malformed source position: " ^ msg
  | `TryCompareLoc msg -> "Failed to compare source spans: " ^ msg
  | `TryCompareSrcPos msg -> "Failed to compare source positions: " ^ msg

let disjoint_batches get_loc elms =
  let f_aux disj_batches elm =
    let loc_elm = Ast.lexed_loc (get_loc elm) in
    match disj_batches with
    | [] -> Ok [ ([ elm ], loc_elm) ]
    | (batch_elms, loc_batch) :: t_disj_batches -> (
        let* rel = rel loc_elm loc_batch in
        match rel with
        | None -> Error (`DisjointBatches "Elements with unrelated locations")
        | Disjoint _ -> Ok (([ elm ], loc_elm) :: disj_batches)
        | Overlapping { kind } ->
            let loc_batch =
              match kind with
              | Partial d -> d.union
              | Inclusion { kind } -> (
                  match kind with
                  | RightInLeft -> loc_elm
                  | LeftInRight -> loc_batch)
              | Eq -> loc_elm
            in
            Ok ((elm :: batch_elms, loc_batch) :: t_disj_batches))
  in
  let* dbs = ListAux.try_fold_left f_aux [] elms in
  let dbs = List.map (fun (es, l) -> (List.rev es, l)) dbs in
  Ok (List.rev dbs)

let loc_contains_srcpos (l : Ast.loc) (pos : Ast.srcpos) =
  let ((path1, line1, col1), (path2, line2, col2)) = lexed_loc l in
  let (path, line, col) = pos in
  path = path1 && path = path2 &&
  (line1 < line || line1 = line && col1 <= col) &&
  (line < line2 || line = line2 && col <= col2)
