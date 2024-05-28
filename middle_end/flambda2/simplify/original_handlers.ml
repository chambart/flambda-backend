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

type t =
  | Recursive of
      { invariant_params : Bound_parameters.t;
        lifted_params : Lifted_cont_params.t;
        continuation_handlers : One_recursive_handler.t Continuation.Map.t
      }
  | Non_recursive of Non_recursive_handler.t

let print ppf t =
  match t with
  | Non_recursive non_rec_handler ->
    Non_recursive_handler.print ppf non_rec_handler
  | Recursive { invariant_params; lifted_params; continuation_handlers } ->
    Format.fprintf ppf
      "@[<hov 1>(@[<hv 1>(invariant params@ %a)@]@ @[<hv 1>(lifted_params@ \
       %a)@]@ @[<hv 1>(continuation handlers@ %a)@])@]"
      Bound_parameters.print invariant_params Lifted_cont_params.print
      lifted_params
      (Continuation.Map.print One_recursive_handler.print)
      continuation_handlers

let add_params_to_lift t params_to_lift =
  let lifted_params, renaming = Lifted_cont_params.rename params_to_lift in
  match t with
  | Recursive
      ({ lifted_params = old_lifted; continuation_handlers; _ } as recursive) ->
    if Lifted_cont_params.is_empty old_lifted
    then
      let continuation_handlers =
        Continuation.Map.map
          (fun (one_rec_handler : One_recursive_handler.t) ->
            let handler =
              Flambda.Expr.apply_renaming one_rec_handler.handler renaming
            in
            { one_rec_handler with handler })
          continuation_handlers
      in
      Recursive { recursive with lifted_params; continuation_handlers }
    else
      Misc.fatal_errorf
        "Cannot add lifted params to a continuation that already has lifted \
         params"
  | Non_recursive ({ lifted_params = old_lifted; handler; _ } as non_rec) ->
    if Lifted_cont_params.is_empty old_lifted
    then
      let handler = Flambda.Expr.apply_renaming handler renaming in
      Non_recursive { non_rec with lifted_params; handler }
    else
      Misc.fatal_errorf
        "Cannot add lifted params to a continuation that already has lifted \
         params"
