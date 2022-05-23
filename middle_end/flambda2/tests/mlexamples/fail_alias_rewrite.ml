
let f b x y =
  if Sys.opaque_identity b then assert false;
  let u = Sys.opaque_identity x in
  let u = u +. 3.14 in
  let v = ref u in
  for i = 0 to 10 do
    Sys.opaque_identity ()
  done;
  !v +. 12.12
