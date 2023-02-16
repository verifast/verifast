type mangled = { mangled_name :string; name: string }

type t = 
  | Normal of string
  | Mangled of mangled

let of_string s = Normal s

let of_mangled ?name mangled_name = 
  match name with
  | Some name -> Mangled { mangled_name; name }
  | None -> Mangled { mangled_name; name = mangled_name }

let id = function
  | Normal s -> s
  | Mangled { mangled_name; _ } -> mangled_name

let name = function
  | Normal s -> s
  | Mangled { name; _ } -> name

let map f = function
  | Normal s -> f s |> of_string
  | Mangled { mangled_name; name } -> 
    let mangled_name, name = f mangled_name, f name in
    of_mangled ~name mangled_name
  