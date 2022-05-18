(* let g b x =
 *   let a, w =
 *     if Sys.opaque_identity b then
 *       Sys.opaque_identity x, 3
 *     else
 *       assert false
 *   in
 *   let _ = Sys.opaque_identity w in
 *   if Sys.opaque_identity b then assert false;
 *   a
 * 
 * let f b x y =
 *   let a = (g [@inlined]) b x in
 *   let v = ref a in
 *   for i = 0 to 10 do
 *     Sys.opaque_identity ()
 *   done;
 *   !v *)

let f b x =
  let a =
    let u = Sys.opaque_identity x in
    if Sys.opaque_identity b then
      assert false
    else
      u
  in
  let v = ref a in
  for i = 0 to 10 do
    Sys.opaque_identity ()
  done;
  !v
