(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2018--2021 OCamlPro SAS                                    *)
(*   Copyright 2018--2021 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

[@@@ocaml.warning "+a-30-40-41-42"]

(** Transformation of types into structures that can be used immediately to
    build terms. *)

type to_lift =
  (* private *)
  (* CR mshinwell: resurrect *)
  | Immutable_block of
      { tag : Tag.Scannable.t;
        is_unique : bool;
        fields : Simple.t list
      }
  | Boxed_float of Numeric_types.Float_by_bit_pattern.t
  | Boxed_int32 of Numeric_types.Int32.t
  | Boxed_int64 of Numeric_types.Int64.t
  | Boxed_nativeint of Targetint_32_64.t
  | Empty_array

type reification_result = private
  | Lift of to_lift (* CR mshinwell: rename? *)
  | Simple of Simple.t
  | Cannot_reify
  | Invalid

val reify :
  ?allowed_if_free_vars_defined_in:Typing_env.t ->
  ?additional_free_var_criterion:(Variable.t -> bool) ->
  ?disallowed_free_vars:Variable.Set.t ->
  ?allow_unique:bool ->
  Typing_env.t ->
  min_name_mode:Name_mode.t ->
  Type_grammar.t ->
  reification_result
