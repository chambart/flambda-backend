(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2019 OCamlPro SAS                                    *)
(*   Copyright 2014--2019 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

type code_id_in_function_declaration = {
  code_id : Code_id.t ;
  is_required_at_runtime : bool ;
}

type t =
  { funs : code_id_in_function_declaration Function_slot.Map.t;
    in_order : code_id_in_function_declaration Function_slot.Lmap.t
  }

let empty =
  { funs = Function_slot.Map.empty; in_order = Function_slot.Lmap.empty }

let is_empty { funs; _ } = Function_slot.Map.is_empty funs

let create in_order =
  { funs = Function_slot.Map.of_list (Function_slot.Lmap.bindings in_order);
    in_order
  }

let funs t = t.funs

let funs_in_order t = t.in_order

let find ({ funs; _ } : t) function_slot =
  Function_slot.Map.find function_slot funs

let [@ocamlformat "disable"] print ppf { in_order; _ } =
  Format.fprintf ppf "@[<hov 1>(%a)@]"
    (Function_slot.Lmap.print
       (fun ppf { code_id ; is_required_at_runtime } -> Format.fprintf ppf "%a%s" Code_id.print code_id (if is_required_at_runtime then "" else "[deleted]")))
    in_order

let free_names { funs; _ } =
  Function_slot.Map.fold
    (fun function_slot { code_id ; is_required_at_runtime = _ } syms ->
       let syms =         (Name_occurrences.add_function_slot_in_declaration syms function_slot
                             Name_mode.normal)
       in
      Name_occurrences.add_code_id syms
        code_id Name_mode.normal)
    funs Name_occurrences.empty

(* Note: the call to {create} at the end already takes into account the
   permutation applied to the function_declarations in {in_order}, so there is
   no need to apply_renaming the func_decls in the {funs} field. *)
let apply_renaming ({ in_order; _ } as t) renaming =
  let in_order' =
    Function_slot.Lmap.map_sharing
      (fun ({ code_id ; is_required_at_runtime } as t)-> let code_id' = Renaming.apply_code_id renaming code_id in if code_id == code_id' then t else { code_id = code_id' ; is_required_at_runtime })
      in_order
  in
  if in_order == in_order' then t else create in_order'

let ids_for_export { funs; _ } =
  Function_slot.Map.fold
    (fun _function_slot { code_id ; is_required_at_runtime = _ } ids ->
       Ids_for_export.add_code_id ids code_id)
    funs Ids_for_export.empty

let compare { funs = funs1; _ } { funs = funs2; _ } =
  Function_slot.Map.compare (fun { code_id = code_id1 ; is_required_at_runtime = is_required_at_runtime1 } { code_id = code_id2 ; is_required_at_runtime = is_required_at_runtime2 } -> let c = Code_id.compare code_id1 code_id2 in if c = 0 then Bool.compare is_required_at_runtime1 is_required_at_runtime2 else c) funs1 funs2

let filter t ~f =
  let funs = Function_slot.Map.filter f t.funs in
  let in_order = Function_slot.Lmap.filter f t.in_order in
  { funs; in_order }

let binds_function_slot t function_slot =
  Function_slot.Map.mem function_slot t.funs
