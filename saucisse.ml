[@@@ocaml.flambda_o3]

external get: 'a array -> int -> 'a = "%array_safe_get"
(* external get: 'a array -> int -> 'a = "%array_unsafe_get" *)

let maxson cmp a l i =
 let i31 = i in
 let x = ref i31 in
 if cmp (get a i31) (get a (i31+1)) then x := i31+1 else ();
 if cmp (get a !x) (get a (i31+2)) then x := i31+2 else ();
 !x
