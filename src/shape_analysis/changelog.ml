open Ast
open Util

(**
 * A changelog is a list of changes of a text file. It expresses
 * at which positions in the file a text (e.g. an annotation) must
 * be inserted or replaced.
 *)

type changeType =
  Insert    (* Insert right before the location *)
  | Replace (* replace the text covered by the location *)
;;

type change = changeType * loc * string;;

(** Given a string and a changelog, apply the changelog to the string and
 * return the result.
 * precondition: all changes refer to the same file which contents is in str.
 *)
let changelog_apply (str: string) (log: change list): string =
  (* This is a bit tricky because locations (of type loc) talk about
   * line and column numbers and not byte positions. An easy solution
   * would be to extend locations. This is easy if the representation
   * of a location was encapsulated, but that is not the case.
   *)
   
  (* TODO *) 
  "// Shape analyser not integrated yet"
  
;;

    
