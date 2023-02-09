let ( let* ) = Result.bind

exception AuxExcp of string

module ListAux = struct
  let partitioni f l =
    let rec helper idx list sat_list unsat_list =
      match list with
      | [] -> (sat_list, unsat_list)
      | head :: tail ->
          (* length of a list is of type int so idx which is of type int, would never overflow *)
          if f idx head then helper (idx + 1) tail (head :: sat_list) unsat_list
          else helper (idx + 1) tail sat_list (head :: unsat_list)
    in
    let sat, unsat = helper 0 l [] [] in
    (List.rev sat, List.rev unsat)

  let try_map f l =
    let rec helper l mapped_l =
      match l with
      | [] -> Ok mapped_l
      | head :: tail ->
          let* mapped_elm = f head in
          helper tail (mapped_elm :: mapped_l)
    in
    let* mapped_l = helper l [] in
    Ok (List.rev mapped_l)

  let rec try_fold_left f inp l =
    match l with
    | [] -> Ok inp
    | h :: t ->
        let* inp = f inp h in
        try_fold_left f inp t

  let try_partition pred l =
    let f_aux (sat, unsat) elm =
      let* b = pred elm in
      if b then Ok (elm :: sat, unsat) else Ok (sat, elm :: unsat)
    in
    let* sat, unsat = try_fold_left f_aux ([], []) l in
    Ok (List.rev sat, List.rev unsat)

  let is_empty l = match l with [] -> true | _ :: _ -> false
  let first l = match l with [] -> None | fst :: _ -> Some fst

  let rec last l =
    match l with [] -> None | lst :: [] -> Some lst | _ :: tl -> last tl

  let try_merge_sorted_lists try_compare l1 l2 =
    let rec f_aux merged l1 l2 =
      match (l1, l2) with
      | [], _ -> Ok (List.rev merged @ l2)
      | _, [] -> Ok (List.rev merged @ l1)
      | h1 :: t1, h2 :: t2 ->
          let* cmp_res = try_compare h1 h2 in
          if cmp_res <= 0 then f_aux (h1 :: merged) t1 l2
          else f_aux (h2 :: merged) l1 t2
    in
    f_aux [] l1 l2

  let try_sort err_desc try_compare l =
    let compare elm1 elm2 =
      match try_compare elm1 elm2 with
      | Ok i -> i
      | Error err_info -> raise (AuxExcp (err_desc err_info))
    in
    try Ok (List.sort compare l) with AuxExcp msg -> Error (`Sort msg)
  (* Todo @Nima: It is clearer to write a `Result` aware sort function *)
end
