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

[@@@ocaml.warning "+a-30-40-41-42"]

open! Simplify_import

let simplify_array_set original_prim (array_kind : P.Array_kind.t) dacc dbg
    ~array_ty ~result_var =
  let elt_kind = P.Array_kind.element_kind array_kind |> K.With_subkind.kind in
  let array_kind =
    Simplify_common.specialise_array_kind dacc array_kind ~array_ty
  in
  (* CR-someday mshinwell: should do a meet on the new value too *)
  match array_kind with
  | Bottom ->
    let ty = T.bottom K.value (* Unit *) in
    let dacc = DA.add_variable dacc result_var ty in
    Simplified_named.invalid (), dacc
  | Ok array_kind ->
    let elt_kind' =
      P.Array_kind.element_kind array_kind |> K.With_subkind.kind
    in
    assert (K.equal elt_kind elt_kind');
    let named = Named.create_prim original_prim dbg in
    let ty = T.unknown (P.result_kind' original_prim) in
    let dacc = DA.add_variable dacc result_var ty in
    Simplified_named.reachable named ~try_reify:false, dacc

let default_ternary_primitive dacc (prim : P.ternary_primitive) ~arg1 ~arg2
    ~arg3 dbg ~result_var =
  let prim : P.t = Ternary (prim, arg1, arg2, arg3) in
  let named = Named.create_prim prim dbg in
  let ty = T.unknown (P.result_kind' prim) in
  let dacc = DA.add_variable dacc result_var ty in
  Simplified_named.reachable named ~try_reify:false, dacc

let is_var_int_var ~arg1 ~arg2 =
  match
    Simple.must_be_var arg1, Simple.must_be_const arg2
  with
  | Some (var1, _coerc1), Some const ->
    let const =
      match Reg_width_const.descr const with
      | Tagged_immediate n ->
        Targetint_31_63.Imm.to_int_exn (Targetint_31_63.to_targetint n)
      | Naked_immediate _ | Naked_float _ | Naked_int32 _ | Naked_int64 _
      | Naked_nativeint _ ->
        Misc.fatal_errorf "Wrong kind for setfield argument"
    in
    Some (var1, const)
  | _ -> None

let simplify_ternary_primitive dacc original_prim (prim : P.ternary_primitive)
    ~arg1 ~arg1_ty ~arg2 ~arg2_ty:_ ~arg3 ~arg3_ty:_ dbg ~result_var =
  match prim with
  | Array_set (array_kind, _init_or_assign) ->
    simplify_array_set original_prim array_kind dacc dbg ~array_ty:arg1_ty
      ~result_var
  | Block_set (Values { tag = _; size = _; field_kind = _ }, Assignment) ->
    let dacc =
      match is_var_int_var ~arg1 ~arg2 with
      | Some (var1, const) ->
        DA.map_data_flow dacc ~f:(DF.add_set_field var1 const ~value:arg3)
      | None ->
        dacc
    in
    default_ternary_primitive dacc prim ~arg1 ~arg2 ~arg3 dbg ~result_var
  | Block_set
      ( (Values _ | Naked_floats _),
        (Initialization | Assignment | Local_assignment) )
  | Bytes_or_bigstring_set _ | Bigarray_set _ ->
    default_ternary_primitive dacc prim ~arg1 ~arg2 ~arg3 dbg ~result_var
