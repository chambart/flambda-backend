(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2024 OCamlPro SAS                                          *)
(*   Copyright 2024 Jane Street Group LLC                                 *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

type t =
  | Inline_when_known
  | Default_inline

let [@ocamlformat "disable"] print ppf t =
  let fprintf = Format.fprintf in
  match t with
  | Inline_when_known -> fprintf ppf "Inline_when_known"
  | Default_inline -> fprintf ppf "Default_inline"

let equal t1 t2 =
  match t1, t2 with
  | Inline_when_known, Inline_when_known
  | Default_inline, Default_inline ->
    true
  | ( ( Inline_when_known
      | Default_inline ),
      _ ) ->
    false

let is_default t =
  match t with
  | Default_inline -> true
  | Inline_when_known -> false

let from_lambda (_attr : Lambda.parameter_attribute) =
  assert false
(*   match attr with *)
(*   | Inline_when_known -> Inline_when_known *)
(*   | Default_inline -> Default_inline *)
