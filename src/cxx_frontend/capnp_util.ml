type 'a capnp_arr = (Stubs_ast.ro, 'a, Reader.R.array_t) Capnp.Array.t

(**
  [capnp_arr_map f arr] applies [f] to every element of cap'n proto array [arr] and returns a new list containing those elements.
*)
let arr_map (f: 'a -> 'b) (arr: 'a capnp_arr): 'b list =
  (* map array to list first, the map function of capnp traverses the array in reverse order *)
  arr |> Capnp.Array.to_list |> List.map f

(**
  [capnp_arr_iter] applies [f] to every element of cap'n proto array [arr].
*)
let arr_iter (f: 'a -> 'b) (arr: 'a capnp_arr): unit =
  arr |> Capnp.Array.iter ~f