(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*           Nathanaëlle Courant, Pierre Chambart, OCamlPro               *)
(*                                                                        *)
(*   Copyright 2024 OCamlPro SAS                                          *)
(*   Copyright 2024 Jane Street Group LLC                                 *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

let unit_with_body (unit : Flambda_unit.t) (body : Flambda.Expr.t) =
  Flambda_unit.create
    ~return_continuation:(Flambda_unit.return_continuation unit)
    ~exn_continuation:(Flambda_unit.exn_continuation unit)
    ~toplevel_my_region:(Flambda_unit.toplevel_my_region unit)
    ~toplevel_my_ghost_region:(Flambda_unit.toplevel_my_ghost_region unit)
    ~body
    ~module_symbol:(Flambda_unit.module_symbol unit)
    ~used_value_slots:(Flambda_unit.used_value_slots unit)

let pp_datalol = Sys.getenv_opt "DATALOL" <> None

let run ~cmx_loader ~all_code (unit : Flambda_unit.t) =
  let debug_print = Flambda_features.dump_reaper () in
  let Traverse.
        { holed;
          deps;
          kinds;
          fixed_arity_continuations;
          continuation_info;
          code_deps
        } =
    Traverse.run unit
  in
  if debug_print
  then Format.printf "USED %a@." Global_flow_graph.pp_used_graph deps;
  let t0 = Sys.time () in
  let solved_dep = Dep_solver.fixpoint deps in
  let t1 = Sys.time () in
  if debug_print
  then (
    Format.printf "RESULT@ %a@." Dep_solver.pp_result solved_dep.uses;
    Format.printf "Aliases@ %a@." Dep_solver.pp_dual_result solved_dep.aliases);
  let () =
    if debug_print
    then (
      Dot_printer.print_solved_dep solved_dep.uses (Code_id.Map.empty, deps);
      Dot_printer.Dual.print solved_dep.dual_graph)
  in
  let Rebuild.{ body; free_names; all_code; slot_offsets } =
    Rebuild.rebuild ~code_deps ~fixed_arity_continuations ~continuation_info
      kinds solved_dep
      (fun code_id ->
        Code_or_metadata.code_metadata (Exported_code.find_exn all_code code_id))
      holed
  in
  (* Is this what we really want? This keeps all the code that has not been
     deleted by this pass to be exported in the cmx. It looks like this does the
     same thing as [Simplify], but on the other hand, we might not want to
     export un-inlinable functions. *)
  let all_code =
    Exported_code.add_code
      ~keep_code:(fun _ -> true)
      all_code
      (Exported_code.mark_as_imported
         (Flambda_cmx.get_imported_code cmx_loader ()))
  in

  if pp_datalol then begin
    let filename =
      let unit_name =
        Compilation_unit.name_as_string
          (Symbol.compilation_unit (Flambda_unit.module_symbol unit))
      in
      Printf.sprintf "%s.pl" unit_name
    in
    let oc = open_out filename in
    let out_fmt = Format.formatter_of_out_channel oc in
    Global_flow_graph.pp_datalog out_fmt deps;
    Format.fprintf out_fmt "%% TIME: %g@." (t1 -. t0);
    close_out oc
  end;

  let _saucisse = "saucisse" in
  unit_with_body unit body, free_names, all_code, slot_offsets
