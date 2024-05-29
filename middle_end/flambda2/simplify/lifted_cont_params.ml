(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                        Guillaume Bury, OCamlPro                        *)
(*                                                                        *)
(*   Copyright 2023--2024 OCamlPro SAS                                    *)
(*   Copyright 2023--2024 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

type id = int

type t = { new_params_indexed : Bound_parameter.t list } [@@unboxed]

let print ppf { new_params_indexed } =
  Format.fprintf ppf "@[<hov 1>(@[<hov 1>(new_params_indexed@ %a)@])@]"
    (Format.pp_print_list ~pp_sep:(fun ppf () -> Format.fprintf ppf "@ ") Bound_parameter.print)
    new_params_indexed

let empty = { new_params_indexed = [] }

let is_empty { new_params_indexed } =
  match new_params_indexed with
  | [] -> true
  | _ :: _ -> false

let length { new_params_indexed } = List.length new_params_indexed

let new_param t bound_param =
  let new_params_indexed = bound_param :: t.new_params_indexed in
  { new_params_indexed }

let rename t =
  let bindings = t.new_params_indexed in
  let bound_param_list = bindings in
  let bound_params = Bound_parameters.create bound_param_list in
  let new_bound_params = Bound_parameters.rename bound_params in
  let renaming =
    Bound_parameters.renaming bound_params ~guaranteed_fresh:new_bound_params
  in
  let new_params_indexed =
    (Bound_parameters.to_list new_bound_params)
  in
  { new_params_indexed }, renaming

let fold ~init ~f { new_params_indexed } =
  let _, acc = List.fold_left (fun (i,acc) v -> i+1, f i v acc) (0,init) new_params_indexed in
  acc

let find_arg n l =
  let find { new_params_indexed } =
    List.nth_opt new_params_indexed n
  in
  Bound_parameter.simple (Option.get (List.find_map find l))

let args ~callee_lifted_params ~caller_stack_lifted_params =
  fold callee_lifted_params ~init:[] ~f:(fun id _callee_param acc ->
      find_arg id caller_stack_lifted_params :: acc)

let bound_parameters t =
  Bound_parameters.create
  @@ fold t ~init:[] ~f:(fun _id bound_param acc -> bound_param :: acc)
