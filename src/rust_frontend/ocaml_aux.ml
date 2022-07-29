let ( let* ) = Result.bind

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
end
