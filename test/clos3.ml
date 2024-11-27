external nosimp : 'a -> 'a = "%obj_magic"
external (+) : int -> int -> int = "%addint"
external opaque : 'a -> 'a = "%opaque"

let test x1 x2 =
  let y = (x1, x2) in
  let[@inline never][@local never] clo1 () =
    let[@inline never][@local never] clo2 () =
      let (a, b) = y in
      a + b
    in
    let () = () in
    clo2
  in
  let () = () in
  let clo = clo1 () in
  let () = () in
  clo ()