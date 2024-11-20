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

(* CR-someday ncourant: expose only accessors instead of the types *)
type field_elt =
  | Field_top
  | Field_vals of Code_id_or_name.Set.t

type elt =
  | Top
  | Fields of
      { fields : field_elt Global_flow_graph.Field.Map.t;
        uses : Code_id_or_name.Set.t
      }
  | Bottom

module Dual_graph : sig
  type field_elt =
    | Field_top
    | Field_vals of Code_id_or_name.Set.t

  type elt =
    | Top
    | Block of
        { fields : field_elt Global_flow_graph.Field.Map.t;
          sources : Code_id_or_name.Set.t
        }
    | Bottom
end

type use_result = (Code_id_or_name.t, elt) Hashtbl.t

type alias_result = (Code_id_or_name.t, Dual_graph.elt) Hashtbl.t

type 'a unboxed_fields =
  | Not_unboxed of 'a
  | Unboxed of 'a unboxed_fields Global_flow_graph.Field.Map.t

type assigned = Variable.t unboxed_fields Code_id_or_name.Map.t

type result =
  { uses : use_result;
    aliases : alias_result;
    dual_graph : Global_flow_graph.Dual.graph;
    unboxed_fields : assigned;
    changed_representation : Global_flow_graph.Field.t unboxed_fields Code_id_or_name.Map.t;
  }

val pp_elt : Format.formatter -> elt -> unit

val pp_result : Format.formatter -> use_result -> unit

val pp_dual_result : Format.formatter -> alias_result -> unit

val fixpoint : Global_flow_graph.graph -> result
