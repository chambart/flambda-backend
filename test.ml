external (+) : int -> int -> int = "%addint"

let f x y =
  let g a b = x + a + b in 
  let h = g y in
  let[@inline never] z () = h 0 in
  (z, 0)