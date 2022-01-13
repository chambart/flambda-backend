(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2020 OCamlPro SAS                                    *)
(*   Copyright 2014--2020 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

[@@@ocaml.warning "+a-4-30-40-41-42"]

(** Contents of middle-end-specific portion of .cmx files when using Flambda. *)

type t0 = {
  original_compilation_unit : Compilation_unit.t;
  final_typing_env : Flambda2_types.Typing_env.Serializable.t;
  all_code : Exported_code.t;
  exported_offsets : Exported_offsets.t;
  used_closure_vars : Var_within_closure.Set.t;
  table_data : Ids_for_export.Table_data.t;
}

type t = t0 list

let empty = []

let create ~final_typing_env ~all_code ~exported_offsets ~used_closure_vars =
(* XXX Verifier
  let typing_env_exported_ids =
    Flambda2_types.Typing_env.Serializable.all_ids_for_export final_typing_env
  in
  let all_code_exported_ids = Exported_code.all_ids_for_export all_code in
  let exported_ids =
    Ids_for_export.union typing_env_exported_ids all_code_exported_ids
  in
  let symbols =
    Symbol.Set.fold
      (fun symbol symbols ->
        Symbol.Map.add symbol (Symbol.export symbol) symbols)
      exported_ids.symbols Symbol.Map.empty
  in
  let variables =
    Variable.Set.fold
      (fun variable variables ->
        Variable.Map.add variable (Variable.export variable) variables)
      exported_ids.variables Variable.Map.empty
  in
  let simples =
    Reg_width_things.Simple.Set.fold
      (fun simple simples ->
        Simple.Map.add simple (Simple.export simple) simples)
      exported_ids.simples Simple.Map.empty
  in
  let consts =
    Const.Set.fold
      (fun const consts -> Const.Map.add const (Const.export const) consts)
      exported_ids.consts Const.Map.empty
  in
  let code_ids =
    Code_id.Set.fold
      (fun code_id code_ids ->
        Code_id.Map.add code_id (Code_id.export code_id) code_ids)
      exported_ids.code_ids Code_id.Map.empty
  in
  let continuations =
    Continuation.Set.fold
      (fun continuation continuations ->
        Continuation.Map.add continuation
          (Continuation.export continuation)
          continuations)
      exported_ids.continuations Continuation.Map.empty
  in
  let table_data =
    { symbols; variables; simples; consts; code_ids; continuations }
  in
  [ { original_compilation_unit = Compilation_unit.get_current_exn ();
      final_typing_env;
      all_code;
      exported_offsets;
      used_closure_vars;
      table_data
    } ]

let import_typing_env_and_code0 t =
  (* First create map for data that does not contain ids, i.e. everything except
     simples *)
  let filter import key data =
    let new_key = import data in
    if key == new_key then None else Some new_key
  in
  let symbols =
    Symbol.Map.filter_map (filter Symbol.import) t.table_data.symbols
  in
  let variables =
    Variable.Map.filter_map (filter Variable.import) t.table_data.variables
  in
  let simples =
    Simple.Map.filter_map (filter Simple.import) t.table_data.simples
  in
  let consts = Const.Map.filter_map (filter Const.import) t.table_data.consts in
  let code_ids =
    Code_id.Map.filter_map (filter Code_id.import) t.table_data.code_ids
  in
  let continuations =
    Continuation.Map.filter_map
      (filter Continuation.import)
      t.table_data.continuations
  in
  let used_closure_vars = t.used_closure_vars in
  let original_compilation_unit = t.original_compilation_unit in
  let renaming =
    Renaming.create_import_map ~symbols ~variables ~simples ~consts ~code_ids
      ~continuations ~used_closure_vars ~original_compilation_unit
*)
  let table_data =
    Typing_env.Serializable.all_ids_for_export final_typing_env
    |> Ids_for_export.Table_data.create
  in
  [{ original_compilation_unit = Compilation_unit.get_current_exn ();
     final_typing_env;
     all_code;
     exported_offsets;
     used_closure_vars;
     table_data;
  }]

let import_typing_env_and_code0 t =
  let renaming =
    Ids_for_export.Table_data.to_import_renaming t.table_data
      ~used_closure_vars:t.used_closure_vars
      ~original_compilation_unit:t.original_compilation_unit
  in
  let typing_env =
    Flambda2_types.Typing_env.Serializable.apply_renaming t.final_typing_env
      renaming
  in
  (* XXX APPLY RENAMING TO CODE *)
  typing_env, t.all_code

let import_typing_env_and_code t =
  match t with
  | [] -> Misc.fatal_error "Flambda cmx info should never be empty"
  | [t0] -> import_typing_env_and_code0 t0
  | t0 :: rem ->
    List.fold_left
      (fun (typing_env, code) t0 ->
        let typing_env0, code0 = import_typing_env_and_code0 t0 in
        let typing_env =
          Flambda2_types.Typing_env.Serializable.merge typing_env typing_env0
        in
        let code = Exported_code.merge code code0 in
        typing_env, code)
      (import_typing_env_and_code0 t0)
      rem

let exported_offsets t =
  List.fold_left
    (fun offsets t0 -> Exported_offsets.merge offsets t0.exported_offsets)
    Exported_offsets.empty t

let functions_info t =
  List.fold_left
    (fun code t0 -> Exported_code.merge code t0.all_code)
    Exported_code.empty t

let with_exported_offsets t exported_offsets =
  match t with
  | [t0] -> [{ t0 with exported_offsets }]
  | [] | _ :: _ :: _ ->
    Misc.fatal_error "Cannot set exported offsets on multiple units"

let update_for_pack0 ~pack_units ~pack t =
(* XXX verifier
  let update_cu unit =
    if Compilation_unit.Set.mem unit pack_units then pack else unit
  in
  let symbols =
    Symbol.Map.map_sharing
      (Symbol.map_compilation_unit update_cu)
      t.table_data.symbols
  in
  let variables =
    Variable.Map.map_sharing
      (Variable.map_compilation_unit update_cu)
      t.table_data.variables
  in
  let simples =
    Simple.Map.map_sharing
      (Simple.map_compilation_unit update_cu)
      t.table_data.simples
  in
  let consts =
    Const.Map.map_sharing
      (Const.map_compilation_unit update_cu)
      t.table_data.consts
  in
  let code_ids =
    Code_id.Map.map_sharing
      (Code_id.map_compilation_unit update_cu)
      t.table_data.code_ids
  in
  let continuations =
    Continuation.Map.map_sharing
      (Continuation.map_compilation_unit update_cu)
      t.table_data.continuations
  in
  let table_data =
    { symbols; variables; simples; consts; code_ids; continuations }
*)
  let table_data =
    Ids_for_export.Table_data.update_for_pack t.table_data ~pack_units ~pack
  in
  { t with table_data }

let update_for_pack ~pack_units ~pack t_opt =
  match t_opt with
  | None -> None
  | Some t -> Some (List.map (update_for_pack0 ~pack_units ~pack) t)

let merge t1_opt t2_opt =
  match t1_opt, t2_opt with
  | None, None -> None
  | Some _, None | None, Some _ ->
    (* CR vlaviron: turn this into a proper user error *)
    Misc.fatal_error
      "Some pack units do not have their export info set.\n\
       Flambda doesn't support packing opaque and normal units together."
  | Some t1, Some t2 -> Some (t1 @ t2)

let print0 ppf t =
  Format.fprintf ppf "@[<hov>Original unit:@ %a@]@;" Compilation_unit.print
    t.original_compilation_unit;
  Compilation_unit.set_current t.original_compilation_unit;
  let typing_env, code = import_typing_env_and_code0 t in
  Format.fprintf ppf "@[<hov>Typing env:@ %a@]@;"
    Flambda2_types.Typing_env.Serializable.print typing_env;
  Format.fprintf ppf "@[<hov>Code:@ %a@]@;" Exported_code.print code;
  Format.fprintf ppf "@[<hov>Offsets:@ %a@]@;" Exported_offsets.print
    t.exported_offsets

let [@ocamlformat "disable"] print ppf t =
  let rec print_rest ppf = function
    | [] -> ()
    | t0 :: t ->
      Format.fprintf ppf "@ (%a)"
        print0 t0;
      print_rest ppf t
  in
  match t with
  | [] -> assert false
  | [ t0 ] -> print0 ppf t0
  | t0 :: t ->
    Format.fprintf ppf "Packed units:@ @[<v>(%a)%a@]"
      print0 t0 print_rest t

type header_for_cmx_file = {
  t : t;
  code_sections_map : int Code_id.Map.t;
}

let create_code_sections_map t ~f =
  ListLabels.fold_left t ~init:Code_id.Map.empty
    ~f:(fun map t0 ->
      Exported_code.fold_for_cmx t0.all_code ~init:map
        ~f:(fun map code_id code_for_cmx ->
          let index = f code_for_cmx in
          Code_id.Map.add code_id index map))

let header_contents t ~add_code_section =
  let code_sections_map = create_code_sections_map t ~f:add_code_section in
  let t =
    ListLabels.map t ~f:(fun t0 ->
      { t0 with
        all_code = Exported_code.prepare_for_cmx_header_section t0.all_code;
      })
  in
  let header =
    { t;
      code_sections_map;
    }
  in
  Obj.repr header

let associate_with_loaded_cmx_file ~header_contents
      ~read_flambda_section_from_cmx_file =
  let header : header_for_cmx_file = Obj.obj header_contents in
  ListLabels.map header.t ~f:(fun t0 ->
    let all_code =
      Exported_code.associate_with_loaded_cmx_file t0.all_code
        ~read_flambda_section_from_cmx_file
        ~code_sections_map:header.code_sections_map
        ~used_closure_vars:t0.used_closure_vars
        ~original_compilation_unit:t0.original_compilation_unit
    in
    { t0 with all_code; })
