(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*    Pierre Chambart and Guillaume Bury, OCamlPro                        *)
(*                                                                        *)
(*   Copyright 2021--2021 OCamlPro SAS                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

module EPA = Continuation_extra_params_and_args

(* Helper module *)
(* ************* *)

module Reachable_code_ids = struct
  type t =
    { live_code_ids : Code_id.Set.t;
      ancestors_of_live_code_ids : Code_id.Set.t
    }

  let [@ocamlformat "disable"] print ppf { live_code_ids; ancestors_of_live_code_ids; } =
    Format.fprintf ppf "@[<hov 1>(\
        @[<hov 1>(live_code_ids@ %a)@]@ \
        @[<hov 1>(ancestors_of_live_code_ids@ %a)@]\
      )@]"
      Code_id.Set.print live_code_ids
      Code_id.Set.print ancestors_of_live_code_ids
end

(* Typedefs *)
(* ******** *)

(* CR chambart/gbury: we might want to also track function_slots in addition to
   value_slots. *)

(* CR-someday chambart/gbury: get rid of Name_occurences everywhere, this is not
   small while we need only the names

   mshinwell: in practice I'm not sure this will make any difference *)
module Cont_arg = struct
  type t =
    | Function_result
    | Simple of Simple.t
    | New_let_binding of Variable.t * Name_occurrences.t

  let print ppf = function
    | Function_result -> Format.fprintf ppf "Function_result"
    | Simple s -> Simple.print ppf s
    | New_let_binding (v, _) ->
      Format.fprintf ppf "New_let_binding %a" Variable.print v
end

type ref_prim =
  | Block_load of
      Flambda_primitive.Block_access_kind.t * Mutability.t * Variable.t * int
  | Block_set of
      Flambda_primitive.Block_access_kind.t
      * Flambda_primitive.Init_or_assign.t
      * Variable.t
      * int
      * Simple.t
  | Make_block of
      Flambda_primitive.Block_kind.t
      * Mutability.t
      * Alloc_mode.With_region.t
      * Simple.t list

type elt =
  { continuation : Continuation.t;
    recursive : bool;
    is_exn_handler : bool;
    params : Bound_parameters.t;
    parent_continuation : Continuation.t option;
    used_in_handler : Name_occurrences.t;
    bindings : Name_occurrences.t Name.Map.t;
    direct_aliases : Simple.t Variable.Map.t;
    ref_prims_rev : (Named_rewrite_id.t * Variable.t * ref_prim) list;
    defined : Variable.Set.t;
    code_ids : Name_occurrences.t Code_id.Map.t;
    value_slots : Name_occurrences.t Name.Map.t Value_slot.Map.t;
    apply_cont_args :
      Cont_arg.t Numeric_types.Int.Map.t Apply_cont_rewrite_id.Map.t
      Continuation.Map.t
  }

type t =
  { stack : elt list;
    map : elt Continuation.Map.t;
    extra : EPA.t Continuation.Map.t;
    dummy_toplevel_cont : Continuation.t
  }

(* type alias useful for later *)
type source_info = t

type recursive_continuation_wrapper =
  | No_wrapper
  | Wrapper_needed

type continuation_parameters =
  { removed_aliased_params_and_extra_params : Variable.Set.t;
    lets_to_introduce : Variable.t Variable.Map.t;
    extra_args_for_aliases : Variable.Set.t;
    recursive_continuation_wrapper : recursive_continuation_wrapper
  }

type continuation_param_aliases =
  { aliases_kind : Flambda_kind.t Variable.Map.t;
    continuation_parameters : continuation_parameters Continuation.Map.t
  }

type dead_variable_result =
  { required_names : Name.Set.t;
    reachable_code_ids : Reachable_code_ids.t
  }

type result =
  { dead_variable_result : dead_variable_result;
    continuation_param_aliases : continuation_param_aliases
  }

(* Print *)
(* ***** *)

let print_ref_prim ppf ref_prim =
  match ref_prim with
  | Block_load (_, _, block, field) ->
    Format.fprintf ppf "Block_load (%a, %i)" Variable.print block field
  | Block_set (_, _, block, field, value) ->
    Format.fprintf ppf "Block_set (%a, %i, %a)" Variable.print block field
      Simple.print value
  | Make_block (_, _, _, args) ->
    Format.fprintf ppf "Make_block [%a]" Simple.List.print args

let print_ref_prims_rev ppf ref_prims_rev =
  let print_elt ppf (_id, var, prim) =
    Format.fprintf ppf "%a = %a" Variable.print var print_ref_prim prim
  in
  Format.fprintf ppf "[%a]"
    (Format.pp_print_list print_elt ~pp_sep:Format.pp_print_space)
    (List.rev ref_prims_rev)

let [@ocamlformat "disable"] print_elt ppf
    { continuation;
      recursive;
      is_exn_handler;
      params;
      parent_continuation;
      used_in_handler;
      bindings;
      direct_aliases;
      ref_prims_rev;
      defined;
      code_ids;
      value_slots;
      apply_cont_args
    } =
  Format.fprintf ppf "@[<hov 1>(\
      @[<hov 1>(continuation %a)@]@ \
      %s\
      %s\
      @[<hov 1>(params %a)@]@ \
      @[<hov 1>(parent_continuation %a)@]@ \
      @[<hov 1>(used_in_handler %a)@]@ \
      @[<hov 1>(bindings %a)@]@ \
      @[<hov 1>(direct_aliases %a)@]@ \
      @[<hov 1>(ref_prims %a)@]@ \
      @[<hov 1>(defined %a)@]@ \
      @[<hov 1>(code_ids %a)@]@ \
      @[<hov 1>(value_slots %a)@]@ \
      @[<hov 1>(apply_cont_args %a)@]\
    )@]"
    Continuation.print continuation
    (if recursive then "(recursive) " else "")
    (if is_exn_handler then "(exn_handler) " else "")
    Bound_parameters.print params
    (Format.pp_print_option ~none:(fun ppf () -> Format.fprintf ppf "root")
       Continuation.print) parent_continuation
    Name_occurrences.print used_in_handler
    (Name.Map.print Name_occurrences.print) bindings
    (Variable.Map.print Simple.print) direct_aliases
    print_ref_prims_rev ref_prims_rev
    Variable.Set.print
    defined
    (Code_id.Map.print Name_occurrences.print)
    code_ids
    (Value_slot.Map.print (Name.Map.print Name_occurrences.print))
    value_slots
    (Continuation.Map.print (Apply_cont_rewrite_id.Map.print
      (Numeric_types.Int.Map.print Cont_arg.print)))
    apply_cont_args

let print_stack ppf stack =
  Format.fprintf ppf "@[<v 1>(%a)@]"
    (Format.pp_print_list print_elt ~pp_sep:Format.pp_print_space)
    stack

let print_map ppf map = Continuation.Map.print print_elt ppf map

let print_extra ppf extra = Continuation.Map.print EPA.print ppf extra

let [@ocamlformat "disable"] print_continuation_parameters ppf
    { removed_aliased_params_and_extra_params; lets_to_introduce;
      extra_args_for_aliases; recursive_continuation_wrapper } =
  let pp_wrapper ppf = function
    | No_wrapper -> ()
    | Wrapper_needed ->
      Format.fprintf ppf "@ @[<hov 1>(recursive_continuation_wrapper needed)@]"
  in
  Format.fprintf ppf
    "@[<hov 1>(\
      @[<hov 1>(removed_aliased_params_and_extra_params %a)@]@ \
      @[<hov 1>(lets_to_introduce %a)@]\
      @[<hov 1>(extra_args_for_aliases %a)@]\
      %a\
     )@]"
    Variable.Set.print removed_aliased_params_and_extra_params
    (Variable.Map.print Variable.print) lets_to_introduce
    Variable.Set.print extra_args_for_aliases
    pp_wrapper recursive_continuation_wrapper

let [@ocamlformat "disable"] print ppf { stack; map; extra; dummy_toplevel_cont = _ } =
  Format.fprintf ppf
    "@[<hov 1>(\
      @[<hov 1>(stack %a)@]@ \
      @[<hov 1>(map %a)@]@ \
      @[<hov 1>(extra %a)@]\
      )@]"
    print_stack stack
    print_map map
    print_extra extra

let [@ocamlformat "disable"] print_continuation_param_aliases ppf
    { aliases_kind; continuation_parameters } =
  Format.fprintf ppf
    "@[<hov 1>(\
       @[<hov 1>(aliases_kind@ %a)@]@ \
       @[<hov 1>(continuation_parameters@ %a)@]\
     )@]"
    (Variable.Map.print Flambda_kind.print) aliases_kind
    (Continuation.Map.print print_continuation_parameters) continuation_parameters

let [@ocamlformat "disable"] _print_result ppf
    { dead_variable_result = { required_names; reachable_code_ids };
      continuation_param_aliases = { aliases_kind; continuation_parameters } } =
  Format.fprintf ppf
    "@[<hov 1>(\
       @[<hov 1>(required_names@ %a)@]@ \
       @[<hov 1>(reachable_code_ids@ %a)@]@ \
       @[<hov 1>(aliases_kind@ %a)@]@ \
       @[<hov 1>(continuation_parameters@ %a)@]\
     )@]"
    Name.Set.print required_names
    Reachable_code_ids.print reachable_code_ids
    (Variable.Map.print Flambda_kind.print) aliases_kind
    (Continuation.Map.print print_continuation_parameters) continuation_parameters

(* Creation *)
(* ******** *)

let wrong_dummy_toplevel_cont_name = "wrong toplevel cont"

let empty () =
  let wrong_dummy_toplevel_cont =
    Continuation.create ~name:wrong_dummy_toplevel_cont_name ()
  in
  { stack = [];
    map = Continuation.Map.empty;
    extra = Continuation.Map.empty;
    dummy_toplevel_cont = wrong_dummy_toplevel_cont
  }

let add_extra_args_to_call ~extra_args rewrite_id original_args =
  match Apply_cont_rewrite_id.Map.find rewrite_id extra_args with
  | exception Not_found -> original_args
  | extra_args ->
    let args_acc =
      if Numeric_types.Int.Map.is_empty original_args
      then 0, Numeric_types.Int.Map.empty
      else
        let max_arg, _ = Numeric_types.Int.Map.max_binding original_args in
        max_arg + 1, original_args
    in
    let extra_args =
      List.map
        (function
          | EPA.Extra_arg.Already_in_scope s -> Cont_arg.Simple s
          | EPA.Extra_arg.New_let_binding (v, prim) ->
            Cont_arg.New_let_binding (v, Flambda_primitive.free_names prim)
          | EPA.Extra_arg.New_let_binding_with_named_args (v, _) ->
            Cont_arg.New_let_binding (v, Name_occurrences.empty))
        extra_args
    in
    let _, args =
      List.fold_left
        (fun (i, args) extra_arg ->
          i + 1, Numeric_types.Int.Map.add i extra_arg args)
        args_acc extra_args
    in
    args

let extend_args_with_extra_args t =
  let map =
    Continuation.Map.map
      (fun elt ->
        let apply_cont_args =
          Continuation.Map.mapi
            (fun cont rewrite_ids ->
              match Continuation.Map.find cont t.extra with
              | exception Not_found -> rewrite_ids
              | epa ->
                let extra_args = EPA.extra_args epa in
                Apply_cont_rewrite_id.Map.mapi
                  (add_extra_args_to_call ~extra_args)
                  rewrite_ids)
            elt.apply_cont_args
        in
        { elt with apply_cont_args })
      t.map
  in
  let map =
    Continuation.Map.map
      (fun elt ->
        let defined =
          Continuation.Map.fold
            (fun callee_cont rewrite_ids defined ->
              match Continuation.Map.find callee_cont t.extra with
              | exception Not_found -> defined
              | epa ->
                Apply_cont_rewrite_id.Map.fold
                  (fun rewrite_id _args defined ->
                    match
                      Apply_cont_rewrite_id.Map.find rewrite_id
                        (EPA.extra_args epa)
                    with
                    | exception Not_found -> defined
                    | extra_args ->
                      let defined =
                        List.fold_left
                          (fun defined -> function
                            | EPA.Extra_arg.Already_in_scope _ -> defined
                            | EPA.Extra_arg.New_let_binding (v, _)
                            | EPA.Extra_arg.New_let_binding_with_named_args
                                (v, _) ->
                              Variable.Set.add v defined)
                          defined extra_args
                      in
                      defined)
                  rewrite_ids defined)
            elt.apply_cont_args elt.defined
        in
        { elt with defined })
      map
  in
  let map =
    Continuation.Map.fold
      (fun cont epa map ->
        let elt = Continuation.Map.find cont map in
        let elt =
          let params =
            Bound_parameters.append elt.params (EPA.extra_params epa)
          in
          { elt with params }
        in
        Continuation.Map.add cont elt map)
      t.extra map
  in
  { t with map }

(* Updates *)
(* ******* *)

let add_extra_params_and_args cont extra t =
  let extra =
    Continuation.Map.update cont
      (function
        | Some _ -> Misc.fatal_errorf "Continuation extended a second time"
        | None -> Some extra)
      t.extra
  in
  { t with extra }

let enter_continuation continuation ~recursive ~is_exn_handler params t =
  let parent_continuation =
    match t.stack with [] -> None | parent :: _ -> Some parent.continuation
  in
  let elt =
    { continuation;
      recursive;
      is_exn_handler;
      params;
      parent_continuation;
      bindings = Name.Map.empty;
      direct_aliases = Variable.Map.empty;
      ref_prims_rev = [];
      defined = Variable.Set.empty;
      code_ids = Code_id.Map.empty;
      value_slots = Value_slot.Map.empty;
      used_in_handler = Name_occurrences.empty;
      apply_cont_args = Continuation.Map.empty
    }
  in
  { t with stack = elt :: t.stack }

let init_toplevel ~dummy_toplevel_cont params _t =
  enter_continuation dummy_toplevel_cont ~recursive:false ~is_exn_handler:false
    params
    { (empty ()) with dummy_toplevel_cont }

let exit_continuation cont t =
  match t.stack with
  | [] -> Misc.fatal_errorf "Empty stack of variable uses"
  | ({ continuation; _ } as elt) :: stack ->
    assert (Continuation.equal cont continuation);
    let map = Continuation.Map.add cont elt t.map in
    { t with stack; map }

let update_top_of_stack ~t ~f =
  match t.stack with
  | [] -> Misc.fatal_errorf "Empty stack of variable uses"
  | elt :: stack -> { t with stack = f elt :: stack }

let record_defined_var var t =
  update_top_of_stack ~t ~f:(fun elt ->
      let defined = Variable.Set.add var elt.defined in
      { elt with defined })

let record_var_binding var name_occurrences ~generate_phantom_lets t =
  update_top_of_stack ~t ~f:(fun elt ->
      let bindings =
        Name.Map.update (Name.var var)
          (function
            | None -> Some name_occurrences
            | Some _ ->
              Misc.fatal_errorf
                "The following variable has been bound twice: %a" Variable.print
                var)
          elt.bindings
      in
      let used_in_handler =
        if Variable.user_visible var && generate_phantom_lets
        then
          Name_occurrences.add_variable elt.used_in_handler var
            Name_mode.phantom
        else elt.used_in_handler
      in
      let defined = Variable.Set.add var elt.defined in
      { elt with bindings; used_in_handler; defined })

let record_ref_named rewrite_id bound_to prim t =
  update_top_of_stack ~t ~f:(fun elt ->
      { elt with
        ref_prims_rev = (rewrite_id, bound_to, prim) :: elt.ref_prims_rev
      })

let record_symbol_projection var name_occurrences t =
  update_top_of_stack ~t ~f:(fun elt ->
      let bindings =
        Name.Map.update (Name.var var)
          (function
            | None -> Some name_occurrences
            | Some prior_occurences as original ->
              if Name_occurrences.equal prior_occurences name_occurrences
              then original
              else
                Misc.fatal_errorf
                  "@[<v>The following projection has been bound to different \
                   symbols:%a@ previously bound to:@ %a@ and now to@ %a@]"
                  Variable.print var Name_occurrences.print prior_occurences
                  Name_occurrences.print name_occurrences)
          elt.bindings
      in
      { elt with bindings })

let record_symbol_binding symbol name_occurrences t =
  update_top_of_stack ~t ~f:(fun elt ->
      let bindings =
        Name.Map.update (Name.symbol symbol)
          (function
            | None -> Some name_occurrences
            | Some _ ->
              Misc.fatal_errorf "The following symbol has been bound twice: %a"
                Symbol.print symbol)
          elt.bindings
      in
      { elt with bindings })

let record_code_id_binding code_id name_occurrences t =
  update_top_of_stack ~t ~f:(fun elt ->
      let code_ids =
        Code_id.Map.update code_id
          (function
            | None -> Some name_occurrences
            | Some _ ->
              Misc.fatal_errorf "The following code_id has been bound twice: %a"
                Code_id.print code_id)
          elt.code_ids
      in
      { elt with code_ids })

let record_value_slot src value_slot dst t =
  update_top_of_stack ~t ~f:(fun elt ->
      let value_slots =
        Value_slot.Map.update value_slot
          (function
            | None -> Some (Name.Map.singleton src dst)
            | Some map ->
              Some
                (Name.Map.update src
                   (function
                     | None -> Some dst
                     | Some dst' -> Some (Name_occurrences.union dst dst'))
                   map))
          elt.value_slots
      in
      { elt with value_slots })

let add_used_in_current_handler name_occurrences t =
  update_top_of_stack ~t ~f:(fun elt ->
      let used_in_handler =
        Name_occurrences.union elt.used_in_handler name_occurrences
      in
      { elt with used_in_handler })

let add_apply_conts ~result_cont ~exn_cont t =
  update_top_of_stack ~t ~f:(fun elt ->
      let add_func_result cont rewrite_id ~extra_args apply_cont_args =
        Continuation.Map.update cont
          (fun (rewrite_map_opt :
                 Cont_arg.t Numeric_types.Int.Map.t Apply_cont_rewrite_id.Map.t
                 option) ->
            let rewrite_map =
              Option.value ~default:Apply_cont_rewrite_id.Map.empty
                rewrite_map_opt
            in
            let rewrite_map =
              Apply_cont_rewrite_id.Map.update rewrite_id
                (function
                  | Some _ ->
                    Misc.fatal_errorf "Introducing a rewrite id twice %a"
                      Apply_cont_rewrite_id.print rewrite_id
                  | None ->
                    let map =
                      Numeric_types.Int.Map.singleton 0 Cont_arg.Function_result
                    in
                    let _, map =
                      List.fold_left
                        (fun (i, map) (extra_arg, _kind) ->
                          let map =
                            Numeric_types.Int.Map.add i
                              (Cont_arg.Simple extra_arg) map
                          in
                          i + 1, map)
                        (1, map) extra_args
                    in
                    Some map)
                rewrite_map
            in
            Some rewrite_map)
          apply_cont_args
      in
      let apply_cont_args =
        let rewrite_id, exn_cont = exn_cont in
        add_func_result
          (Exn_continuation.exn_handler exn_cont)
          rewrite_id
          ~extra_args:(Exn_continuation.extra_args exn_cont)
          elt.apply_cont_args
      in
      let apply_cont_args =
        match result_cont with
        | None -> apply_cont_args
        | Some (rewrite_id, result_cont) ->
          add_func_result result_cont rewrite_id ~extra_args:[] apply_cont_args
      in
      { elt with apply_cont_args })

let add_apply_cont_args ~rewrite_id cont arg_name_simples t =
  update_top_of_stack ~t ~f:(fun elt ->
      let apply_cont_args =
        Continuation.Map.update cont
          (fun (rewrite_map_opt :
                 Cont_arg.t Numeric_types.Int.Map.t Apply_cont_rewrite_id.Map.t
                 option) ->
            let rewrite_map =
              Option.value ~default:Apply_cont_rewrite_id.Map.empty
                rewrite_map_opt
            in
            let rewrite_map =
              Apply_cont_rewrite_id.Map.update rewrite_id
                (function
                  | Some _ ->
                    Misc.fatal_errorf "Introducing a rewrite id twice %a"
                      Apply_cont_rewrite_id.print rewrite_id
                  | None ->
                    let map, _ =
                      List.fold_left
                        (fun (map, i) arg_simple ->
                          let map =
                            Numeric_types.Int.Map.add i
                              (Cont_arg.Simple arg_simple) map
                          in
                          map, i + 1)
                        (Numeric_types.Int.Map.empty, 0)
                        arg_name_simples
                    in
                    Some map)
                rewrite_map
            in
            Some rewrite_map)
          elt.apply_cont_args
      in
      { elt with apply_cont_args })

(* Dependency graph *)
(* **************** *)

module Dependency_graph = struct
  type t =
    { code_age_relation : Code_age_relation.t;
      name_to_name : Name.Set.t Name.Map.t;
      name_to_code_id : Code_id.Set.t Name.Map.t;
      code_id_to_name : Name.Set.t Code_id.Map.t;
      code_id_to_code_id : Code_id.Set.t Code_id.Map.t;
      unconditionally_used : Name.Set.t;
      code_id_unconditionally_used : Code_id.Set.t
    }

  module Reachable = struct
    module Edge (Src_map : Container_types.Map) (Dst_set : Container_types.Set) =
    struct
      type src = Src_map.key

      type dst = Dst_set.elt

      let push ~(src : src) (enqueued : Dst_set.t) (queue : dst Queue.t)
          (graph : Dst_set.t Src_map.t) : Dst_set.t =
        let neighbours =
          match Src_map.find src graph with
          | exception Not_found -> Dst_set.empty
          | set -> set
        in
        let new_neighbours = Dst_set.diff neighbours enqueued in
        Dst_set.iter (fun dst -> Queue.push dst queue) new_neighbours;
        Dst_set.union enqueued new_neighbours
    end
    [@@inline]
    (* TODO check that this applied here *)

    module Name_Name_Edge = Edge (Name.Map) (Name.Set)
    module Name_Code_id_Edge = Edge (Name.Map) (Code_id.Set)
    module Code_id_Name_Edge = Edge (Code_id.Map) (Name.Set)
    module Code_id_Code_id_Edge = Edge (Code_id.Map) (Code_id.Set)

    (* breadth-first reachability analysis. *)
    let rec reachable_names t code_id_queue code_id_enqueued older_enqueued
        name_queue name_enqueued =
      match Queue.take name_queue with
      | exception Queue.Empty ->
        if Queue.is_empty code_id_queue
        then
          { required_names = name_enqueued;
            reachable_code_ids =
              { live_code_ids = code_id_enqueued;
                ancestors_of_live_code_ids = older_enqueued
              }
          }
        else
          reachable_code_ids t code_id_queue code_id_enqueued (Queue.create ())
            older_enqueued name_queue name_enqueued
      | src ->
        let name_enqueued =
          Name_Name_Edge.push ~src name_enqueued name_queue t.name_to_name
        in
        let code_id_enqueued =
          Name_Code_id_Edge.push ~src code_id_enqueued code_id_queue
            t.name_to_code_id
        in
        reachable_names t code_id_queue code_id_enqueued older_enqueued
          name_queue name_enqueued

    and reachable_code_ids t code_id_queue code_id_enqueued older_queue
        older_enqueued name_queue name_enqueued =
      match Queue.take code_id_queue with
      | exception Queue.Empty ->
        if Queue.is_empty older_queue
        then
          reachable_names t code_id_queue code_id_enqueued older_enqueued
            name_queue name_enqueued
        else
          reachable_older_code_ids t code_id_queue code_id_enqueued older_queue
            older_enqueued name_queue name_enqueued
      | src ->
        let name_enqueued =
          Code_id_Name_Edge.push ~src name_enqueued name_queue t.code_id_to_name
        in
        let code_id_enqueued =
          Code_id_Code_id_Edge.push ~src code_id_enqueued code_id_queue
            t.code_id_to_code_id
        in
        let older_enqueued =
          if Code_id.Set.mem src older_enqueued
          then older_enqueued
          else (
            Queue.push src older_queue;
            Code_id.Set.add src older_enqueued)
        in
        reachable_code_ids t code_id_queue code_id_enqueued older_queue
          older_enqueued name_queue name_enqueued

    and reachable_older_code_ids t code_id_queue code_id_enqueued older_queue
        older_enqueued name_queue name_enqueued =
      match Queue.take older_queue with
      | exception Queue.Empty ->
        reachable_code_ids t code_id_queue code_id_enqueued older_queue
          older_enqueued name_queue name_enqueued
      | src -> (
        match
          Code_age_relation.get_older_version_of t.code_age_relation src
        with
        | None ->
          reachable_older_code_ids t code_id_queue code_id_enqueued older_queue
            older_enqueued name_queue name_enqueued
        | Some dst ->
          if Code_id.Set.mem dst older_enqueued
          then (
            if Code_id.Set.mem dst code_id_enqueued
            then
              reachable_older_code_ids t code_id_queue code_id_enqueued
                older_queue older_enqueued name_queue name_enqueued
            else
              let code_id_enqueued = Code_id.Set.add dst code_id_enqueued in
              Queue.push dst code_id_queue;
              reachable_older_code_ids t code_id_queue code_id_enqueued
                older_queue older_enqueued name_queue name_enqueued)
          else
            let older_enqueued = Code_id.Set.add dst older_enqueued in
            reachable_older_code_ids t code_id_queue code_id_enqueued
              older_queue older_enqueued name_queue name_enqueued)
  end

  let empty code_age_relation =
    { code_age_relation;
      name_to_name = Name.Map.empty;
      name_to_code_id = Name.Map.empty;
      code_id_to_name = Code_id.Map.empty;
      code_id_to_code_id = Code_id.Map.empty;
      unconditionally_used = Name.Set.empty;
      code_id_unconditionally_used = Code_id.Set.empty
    }

  let _print ppf
      { name_to_name;
        name_to_code_id;
        code_id_to_name;
        code_id_to_code_id;
        code_age_relation;
        unconditionally_used;
        code_id_unconditionally_used
      } =
    Format.fprintf ppf
      "@[<hov 1>(@[<hov 1>(code_age_relation@ %a)@]@ @[<hov 1>(name_to_name@ \
       %a)@]@ @[<hov 1>(name_to_code_id@ %a)@]@ @[<hov 1>(code_id_to_name@ \
       %a)@]@ @[<hov 1>(code_id_to_code_id@ %a)@]@ @[<hov \
       1>(unconditionally_used@ %a)@]@ @[<hov 1>(code_id_unconditionally_used@ \
       %a)@])@]"
      Code_age_relation.print code_age_relation
      (Name.Map.print Name.Set.print)
      name_to_name
      (Name.Map.print Code_id.Set.print)
      name_to_code_id
      (Code_id.Map.print Name.Set.print)
      code_id_to_name
      (Code_id.Map.print Code_id.Set.print)
      code_id_to_code_id Name.Set.print unconditionally_used Code_id.Set.print
      code_id_unconditionally_used

  (* *)
  let fold_name_occurrences name_occurrences ~init ~names ~code_ids =
    Name_occurrences.fold_names name_occurrences ~f:names
      ~init:(code_ids init (Name_occurrences.code_ids name_occurrences))

  (* Some auxiliary functions *)
  let add_code_id_dep ~src ~(dst : Code_id.Set.t) ({ name_to_code_id; _ } as t)
      =
    let name_to_code_id =
      Name.Map.update src
        (function
          | None -> if Code_id.Set.is_empty dst then None else Some dst
          | Some old ->
            Misc.fatal_errorf "Same name bound multiple times: %a -> %a, %a"
              Name.print src Code_id.Set.print old Code_id.Set.print dst)
        name_to_code_id
    in
    { t with name_to_code_id }

  let add_dependency ~src ~dst ({ name_to_name; _ } as t) =
    let name_to_name =
      Name.Map.update src
        (function
          | None -> Some (Name.Set.singleton dst)
          | Some set -> Some (Name.Set.add dst set))
        name_to_name
    in
    { t with name_to_name }

  let add_code_id_dependency ~src ~dst ({ code_id_to_name; _ } as t) =
    let code_id_to_name =
      Code_id.Map.update src
        (function
          | None -> Some (Name.Set.singleton dst)
          | Some set -> Some (Name.Set.add dst set))
        code_id_to_name
    in
    { t with code_id_to_name }

  let add_code_id_to_code_id ~src ~dst ({ code_id_to_code_id; _ } as t) =
    let code_id_to_code_id =
      Code_id.Map.update src
        (function
          | None -> if Code_id.Set.is_empty dst then None else Some dst
          | Some old ->
            Misc.fatal_errorf "Same code_id bound multiple times: %a -> %a, %a"
              Code_id.print src Code_id.Set.print old Code_id.Set.print dst)
        code_id_to_code_id
    in
    { t with code_id_to_code_id }

  let add_name_occurrences name_occurrences
      ({ unconditionally_used; code_id_unconditionally_used; _ } as t) =
    let unconditionally_used =
      Name_occurrences.fold_names name_occurrences
        ~f:(fun set name -> Name.Set.add name set)
        ~init:unconditionally_used
    in
    let code_id_unconditionally_used =
      Code_id.Set.union
        (Name_occurrences.code_ids name_occurrences)
        code_id_unconditionally_used
    in
    { t with unconditionally_used; code_id_unconditionally_used }

  let ref_prim_free_names (ref_prim : ref_prim) : Name_occurrences.t =
    match ref_prim with
    | Block_load (_, _, block, _field) ->
      Name_occurrences.singleton_variable block Name_mode.normal
    | Block_set (_, _, block, _field, c) ->
      Name_occurrences.add_variable (Simple.free_names c) block Name_mode.normal
    | Make_block (_, _, _, args) -> Simple.List.free_names args

  let add_continuation_info map ~return_continuation ~exn_continuation
      ~used_value_slots _
      { apply_cont_args;
        (* CR pchambart: properly follow dependencies in exception extra args.
           They are currently marked as always used, so it is correct, but not
           optimal *)
        used_in_handler;
        bindings;
        direct_aliases;
        ref_prims_rev;
        defined = _;
        code_ids;
        value_slots;
        continuation = _;
        recursive = _;
        is_exn_handler = _;
        parent_continuation = _;
        params = _
      } t =
    (* Add the vars used in the handler *)
    let t = add_name_occurrences used_in_handler t in
    (* Add the dependencies created by closures vars in envs *)
    let is_value_slot_used =
      match (used_value_slots : _ Or_unknown.t) with
      | Unknown -> fun _ -> true
      | Known used_value_slots ->
        Name_occurrences.value_slot_is_used_or_imported used_value_slots
    in
    let t =
      Value_slot.Map.fold
        (fun value_slot map t ->
          if not (is_value_slot_used value_slot)
          then t
          else
            Name.Map.fold
              (fun closure_name values_in_env t ->
                Name_occurrences.fold_names
                  ~f:(fun t value_in_env ->
                    add_dependency ~src:closure_name ~dst:value_in_env t)
                  values_in_env ~init:t)
              map t)
        value_slots t
    in
    (* Build the graph of dependencies between names *)
    let t =
      Name.Map.fold
        (fun src name_occurrences graph ->
          fold_name_occurrences name_occurrences ~init:graph
            ~names:(fun t dst -> add_dependency ~src ~dst t)
            ~code_ids:(fun t dst -> add_code_id_dep ~src ~dst t))
        bindings t
    in
    let t =
      Variable.Map.fold
        (fun src simple graph ->
          let src = Name.var src in
          let name_occurrences = Simple.free_names simple in
          fold_name_occurrences name_occurrences ~init:graph
            ~names:(fun t dst -> add_dependency ~src ~dst t)
            ~code_ids:(fun t dst -> add_code_id_dep ~src ~dst t))
        direct_aliases t
    in
    let t =
      List.fold_left
        (fun t (_id, src, prim) ->
          let src = Name.var src in
          match prim with
          | Make_block _ | Block_load _ ->
            Name_occurrences.fold_names
              ~f:(fun t dst -> add_dependency ~src ~dst t)
              (ref_prim_free_names prim) ~init:t
          | Block_set _ -> add_name_occurrences (ref_prim_free_names prim) t)
        t ref_prims_rev
    in
    let t =
      Code_id.Map.fold
        (fun src name_occurrences graph ->
          fold_name_occurrences name_occurrences ~init:graph
            ~names:(fun t dst -> add_code_id_dependency ~src ~dst t)
            ~code_ids:(fun t dst -> add_code_id_to_code_id ~src ~dst t))
        code_ids t
    in
    (* Build the graph of dependencies between continuation parameters and
       arguments. *)
    Continuation.Map.fold
      (fun k rewrite_ids t ->
        if Continuation.equal return_continuation k
           || Continuation.equal exn_continuation k
        then
          Apply_cont_rewrite_id.Map.fold
            (fun _rewrite_id args t ->
              Numeric_types.Int.Map.fold
                (fun _ (cont_arg : Cont_arg.t) t ->
                  match cont_arg with
                  | Simple simple ->
                    add_name_occurrences (Simple.free_names simple) t
                  | New_let_binding (var, prim_free_names) ->
                    add_name_occurrences
                      (Name_occurrences.union prim_free_names
                         (Name_occurrences.singleton_variable var
                            Name_mode.normal))
                      t
                  | Function_result -> t)
                args t)
            rewrite_ids t
        else
          let params =
            match Continuation.Map.find k map with
            | elt -> Array.of_list (Bound_parameters.vars elt.params)
            | exception Not_found ->
              Misc.fatal_errorf "Continuation not found during Data_flow: %a@."
                Continuation.print k
          in
          Apply_cont_rewrite_id.Map.fold
            (fun rewrite_id args t ->
              let correct_number_of_arguments =
                match Numeric_types.Int.Map.max_binding args with
                | exception Not_found -> Array.length params = 0
                | max_arg, _ -> max_arg = Array.length params - 1
              in
              if not correct_number_of_arguments
              then
                Misc.fatal_errorf
                  "Mismatched number of argument and params for %a at \
                   rewrite_id %a"
                  Continuation.print k Apply_cont_rewrite_id.print rewrite_id;
              Numeric_types.Int.Map.fold
                (fun i (cont_arg : Cont_arg.t) t ->
                  (* Note on the direction of the edge:

                     We later do a reachability analysis to compute the
                     transitive closure of the used variables.

                     Therefore an edge from src to dst means: if src is used,
                     then dst is also used.

                     Applied here, this means : if the param of a continuation
                     is used, then any argument provided for that param is also
                     used. The other way wouldn't make much sense. *)
                  let src = Name.var params.(i) in
                  match cont_arg with
                  | Simple simple ->
                    Name_occurrences.fold_names (Simple.free_names simple)
                      ~init:t ~f:(fun t dst -> add_dependency ~src ~dst t)
                  | New_let_binding (var, prim_free_names) ->
                    let t = add_dependency ~src ~dst:(Name.var var) t in
                    Name_occurrences.fold_names prim_free_names ~init:t
                      ~f:(fun t dst ->
                        add_dependency ~src:(Name.var var) ~dst t)
                  | Function_result -> t)
                args t)
            rewrite_ids t)
      apply_cont_args t

  let create ~return_continuation ~exn_continuation ~code_age_relation
      ~used_value_slots map =
    (* Build the dependencies using the regular params and args of
       continuations, and the let-bindings in continuations handlers. *)
    let t =
      Continuation.Map.fold
        (add_continuation_info map ~return_continuation ~exn_continuation
           ~used_value_slots)
        map (empty code_age_relation)
    in
    t

  let required_names
      ({ code_age_relation = _;
         name_to_name = _;
         name_to_code_id = _;
         code_id_to_name = _;
         code_id_to_code_id = _;
         unconditionally_used;
         code_id_unconditionally_used
       } as t) =
    let name_queue = Queue.create () in
    Name.Set.iter (fun v -> Queue.push v name_queue) unconditionally_used;
    let code_id_queue = Queue.create () in
    Code_id.Set.iter
      (fun v -> Queue.push v code_id_queue)
      code_id_unconditionally_used;
    Reachable.reachable_names t code_id_queue code_id_unconditionally_used
      Code_id.Set.empty name_queue unconditionally_used
end

(* Dominator graph *)
(* *************** *)

module Dominator_graph = struct
  module G = Strongly_connected_components.Make (Variable)

  type t =
    { required_names : Name.Set.t;
      params_kind : Flambda_kind.With_subkind.t Variable.Map.t;
      graph : G.directed_graph;
      dominator_roots : Variable.Set.t
          (* variables that are dominated only by themselves, usually because a
             constant or a symbol can flow to that variable, and thus that
             variable cannot be dominated by another variable. *)
    }

  type result = Variable.t Variable.Map.t

  let empty ~required_names =
    let graph = Variable.Map.empty in
    let dominator_roots = Variable.Set.empty in
    let params_kind = Variable.Map.empty in
    { required_names; params_kind; graph; dominator_roots }

  let add_node t var =
    if not (Name.Set.mem (Name.var var) t.required_names)
    then t
    else
      let graph =
        Variable.Map.update var
          (function None -> Some Variable.Set.empty | Some _ as res -> res)
          t.graph
      in
      { t with graph }

  let add_root var t =
    if not (Name.Set.mem (Name.var var) t.required_names)
    then t
    else { t with dominator_roots = Variable.Set.add var t.dominator_roots }

  let add_edge ~src ~dst t =
    if not (Name.Set.mem (Name.var src) t.required_names)
    then t
    else
      Simple.pattern_match' dst
        ~const:(fun _ -> add_root src t)
        ~symbol:(fun _ ~coercion:_ -> add_root src t)
        ~var:(fun dst ~coercion:_ ->
          let graph =
            Variable.Map.update src
              (function
                | None -> Some (Variable.Set.singleton dst)
                | Some s -> Some (Variable.Set.add dst s))
              t.graph
          in
          { t with graph })

  let add_continuation_info map _k elt t ~return_continuation ~exn_continuation
      =
    let t =
      List.fold_left
        (fun t bp ->
          let var = Bound_parameter.var bp in
          let t = add_node t var in
          let params_kind =
            Variable.Map.add var (Bound_parameter.kind bp) t.params_kind
          in
          { t with params_kind })
        t
        (Bound_parameters.to_list elt.params)
    in
    let t =
      Variable.Map.fold
        (fun src dst t -> add_edge ~src ~dst t)
        elt.direct_aliases t
    in
    Continuation.Map.fold
      (fun k rewrite_ids t ->
        if Continuation.equal return_continuation k
           || Continuation.equal exn_continuation k
        then t
        else
          let params =
            match Continuation.Map.find k map with
            | elt -> Array.of_list (Bound_parameters.vars elt.params)
            | exception Not_found ->
              Misc.fatal_errorf "Continuation not found during Data_flow: %a@."
                Continuation.print k
          in
          Apply_cont_rewrite_id.Map.fold
            (fun _rewrite_id args t ->
              Numeric_types.Int.Map.fold
                (fun i (dst : Cont_arg.t) t ->
                  (* Note on the direction of the edge:

                     We later do a dominator analysis on this graph. To do so,
                     we consider that an edge from ~src to ~dst means: ~dst is
                     used as argument (of an apply_cont), that maps to ~src (as
                     param of a continuation). *)
                  let src = params.(i) in
                  match dst with
                  | Simple dst -> add_edge ~src ~dst t
                  | Function_result -> add_root src t
                  | New_let_binding (var, _) ->
                    let t = add_root var t in
                    add_edge ~src ~dst:(Simple.var var) t)
                args t)
            rewrite_ids t)
      elt.apply_cont_args t

  let create ~required_names ~return_continuation ~exn_continuation map =
    let t = empty ~required_names in
    let t =
      Continuation.Map.fold
        (add_continuation_info ~return_continuation ~exn_continuation map)
        map t
    in
    let all_variables =
      Variable.Map.fold
        (fun v dsts acc -> Variable.Set.add v (Variable.Set.union dsts acc))
        t.graph t.dominator_roots
    in
    (* ensure that all variable are mapped: this is a requirement for the SCC
       computation *)
    let t =
      Variable.Set.fold
        (fun var t ->
          let graph =
            Variable.Map.update var
              (function
                | Some _ as res -> res | None -> Some Variable.Set.empty)
              t.graph
          in
          { t with graph })
        all_variables t
    in
    (* Format.eprintf "GRAPH:@\n%a@." (Variable.Map.print Variable.Set.print)
       t.graph; *)
    t

  let find_dom var doms =
    (* there are tow cases where the variable is not in the "doms" maps:

       - is not mapped in the graph, which means that it is a let-bound
       variable, in which case it can only be dominated by itself.

       - we are in th efirst iteration of a loop fixpoint, in which case we also
       want to initialize the dominator to the variable itself. *)
    try Variable.Map.find var doms with Not_found -> var

  let update_doms_for_one_var { dominator_roots; graph; _ } doms var =
    let dom =
      if Variable.Set.mem var dominator_roots
      then var
      else
        match Variable.Map.find var graph with
        | exception Not_found -> var
        | predecessors ->
          let s =
            Variable.Set.map
              (fun predecessor -> find_dom predecessor doms)
              predecessors
          in
          if Variable.Set.cardinal s = 1 then Variable.Set.choose s else var
    in
    Variable.Map.add var dom doms

  let initialize_doms_for_fixpoint { graph; _ } doms vars =
    (* Note: since all vars are in a cycle, all_predecessors will include all
       vars *)
    let all_predecessors =
      List.fold_left
        (fun acc var ->
          let predecessors =
            try Variable.Map.find var graph with Not_found -> assert false
          in
          Variable.Set.union predecessors acc)
        Variable.Set.empty vars
    in
    let init_doms =
      Variable.Set.map (fun var -> find_dom var doms) all_predecessors
    in
    let outside_cycle =
      Variable.Map.of_set
        (fun var -> Variable.Set.singleton (find_dom var doms))
        (Variable.Set.diff all_predecessors (Variable.Set.of_list vars))
    in
    List.fold_left
      (fun doms var -> Variable.Map.add var init_doms doms)
      outside_cycle vars

  let rec dom_fixpoint ({ graph; dominator_roots; _ } as t) acc vars =
    let acc' =
      List.fold_left
        (fun acc var ->
          if Variable.Set.mem var dominator_roots
          then Variable.Map.add var (Variable.Set.singleton var) acc
          else
            let init_doms = Variable.Map.find var acc in
            let predecessors =
              try Variable.Map.find var graph with Not_found -> assert false
            in
            let new_doms =
              Variable.Set.fold
                (fun predecessor new_doms ->
                  Variable.Set.inter new_doms
                    (Variable.Map.find predecessor acc))
                predecessors init_doms
            in
            let new_doms = Variable.Set.add var new_doms in
            Variable.Map.add var new_doms acc)
        acc vars
    in
    if Variable.Map.equal Variable.Set.equal acc acc'
    then acc
    else dom_fixpoint t acc' vars

  let extract_doms doms fixpoint_result vars =
    let var_set = Variable.Set.of_list vars in
    List.fold_left
      (fun doms var ->
        let fixpoint_doms = Variable.Map.find var fixpoint_result in
        let var_doms = Variable.Set.diff fixpoint_doms var_set in
        let cardinal = Variable.Set.cardinal var_doms in
        assert (cardinal <= 1);
        let dom = if cardinal = 1 then Variable.Set.choose var_doms else var in
        Variable.Map.add var dom doms)
      doms vars

  let dominator_analysis ({ graph; _ } as t) : result =
    let components = G.connected_components_sorted_from_roots_to_leaf graph in
    let dominators =
      Array.fold_right
        (fun component doms ->
          match component with
          | G.No_loop var -> update_doms_for_one_var t doms var
          | G.Has_loop vars ->
            let loop_doms = initialize_doms_for_fixpoint t doms vars in
            let loop_result = dom_fixpoint t loop_doms vars in
            let doms = extract_doms doms loop_result vars in
            doms)
        components Variable.Map.empty
    in
    dominators

  let aliases_kind { params_kind; required_names; _ } aliases =
    Variable.Map.fold
      (fun param kind acc ->
        if not (Name.Set.mem (Name.var param) required_names)
        then acc
        else
          let alias = Variable.Map.find param aliases in
          (* CR: Not sure this is absolutely necessary, but it's simpler. The
             alternative would be to do a join of all kinds with subkinds for
             all the members of the alias class. *)
          let kind = Flambda_kind.With_subkind.kind kind in
          (match Variable.Map.find alias acc with
          | exception Not_found -> ()
          | alias_kind ->
            if not (Flambda_kind.equal kind alias_kind)
            then Misc.fatal_errorf "Incoherent kinds for aliases !");
          Variable.Map.add alias kind acc)
      params_kind Variable.Map.empty

  module Dot = struct
    let node_id ~ctx ppf (variable : Variable.t) =
      Format.fprintf ppf "node_%d_%d" ctx (variable :> int)

    let node ~ctx ~root ppf var =
      if root
      then
        Format.fprintf ppf "%a [shape=record label=\"%a\"];@\n" (node_id ~ctx)
          var Variable.print var
      else
        Format.fprintf ppf "%a [label=\"%a\"];@\n" (node_id ~ctx) var
          Variable.print var

    let nodes ~ctx ~roots ppf var_map =
      Variable.Map.iter
        (fun var _ ->
          let root = Variable.Set.mem var roots in
          node ~ctx ~root ppf var)
        var_map

    let edge ~ctx ~color ppf src dst =
      Format.fprintf ppf "%a -> %a [color=\"%s\"];@\n" (node_id ~ctx) src
        (node_id ~ctx) dst color

    let edges ~ctx ~color ppf edge_map =
      Variable.Map.iter
        (fun src dst_set ->
          Variable.Set.iter (fun dst -> edge ~ctx ~color ppf src dst) dst_set)
        edge_map

    let edges' ~ctx ~color ppf edge_map =
      Variable.Map.iter (fun src dst -> edge ~ctx ~color ppf src dst) edge_map

    let print ~ctx ~print_name ~doms ppf t =
      Flambda_colours.without_colours ~f:(fun () ->
          Format.fprintf ppf
            "subgraph cluster_%d { label=\"%s\"@\n%a@\n%a@\n%a@\n}@." ctx
            print_name
            (nodes ~ctx ~roots:t.dominator_roots)
            t.graph
            (edges ~ctx ~color:"black")
            t.graph (edges' ~ctx ~color:"red") doms)
  end
end

module Non_escaping_references = struct
  type extra_ref_params = Variable.t list

  type extra_ref_args =
    Cont_arg.t Numeric_types.Int.Map.t Apply_cont_rewrite_id.Map.t
    Continuation.Map.t

  type t =
    { (* non_escaping_references : Variable.Set.t *)
      non_escaping_makeblock : Simple.t list Variable.Map.t;
      continuations_with_live_ref : Variable.Set.t Continuation.Map.t;
      extra_ref_params_and_args :
        (extra_ref_params * extra_ref_args) Continuation.Map.t
    }

  let escaping ~(dom : Dominator_graph.result) ~(dom_graph : Dominator_graph.t)
      ~(source_info : source_info) =
    ignore source_info;
    let escaping_by_alias =
      Variable.Map.fold
        (fun flow_to flow_from escaping ->
          let alias_to =
            match Variable.Map.find flow_to dom with
            | exception Not_found -> flow_to
            | v -> v
          in
          let new_escaping =
            Variable.Set.filter
              (fun flow_from ->
                let alias_from =
                  match Variable.Map.find flow_from dom with
                  | exception Not_found -> flow_from
                  | v -> v
                in
                not (Variable.equal alias_to alias_from))
              flow_from
          in
          Format.printf "From %a to %a@." Variable.Set.print flow_from
            Variable.print flow_to;
          if not (Variable.Set.is_empty new_escaping)
          then
            Format.printf "Escaping by alias %a@." Variable.Set.print
              new_escaping;
          Variable.Set.union escaping new_escaping)
        dom_graph.graph Variable.Set.empty
    in
    let ref_prim_escaping (prim : ref_prim) =
      match prim with
      | Make_block (_, _, _, args) -> Simple.List.free_names args
      | Block_set (_, _, _, _, value) -> Simple.free_names value
      | Block_load _ -> Name_occurrences.empty
    in
    let escaping_by_use elt =
      let add_name_occurrences occurrences init =
        Name_occurrences.fold_variables occurrences ~init
          ~f:(fun escaping var -> Variable.Set.add var escaping)
      in
      let escaping =
        add_name_occurrences elt.used_in_handler Variable.Set.empty
      in
      let escaping =
        Name.Map.fold
          (fun _ deps escaping -> add_name_occurrences deps escaping)
          elt.bindings escaping
      in
      let escaping =
        Value_slot.Map.fold
          (fun _value_slot map escaping ->
            Name.Map.fold
              (fun _closure_name values_in_env escaping ->
                add_name_occurrences values_in_env escaping)
              map escaping)
          elt.value_slots escaping
      in
      let escaping =
        List.fold_left
          (fun escaping (_id, _var, prim) ->
            add_name_occurrences (ref_prim_escaping prim) escaping)
          escaping elt.ref_prims_rev
      in
      escaping
    in
    let escaping_by_use =
      Continuation.Map.fold
        (fun _cont elt escaping ->
          Variable.Set.union (escaping_by_use elt) escaping)
        source_info.map Variable.Set.empty
    in
    if not (Variable.Set.is_empty escaping_by_use)
    then Format.printf "Escaping by use %a@." Variable.Set.print escaping_by_use;
    let escaping_by_return =
      (* TODO mark argument of the return and exn_return cont to be escaping *)
      Variable.Set.empty
    in
    Variable.Set.union escaping_by_alias
      (Variable.Set.union escaping_by_return escaping_by_use)

  let non_escaping_makeblocks ~escaping ~source_info =
    Continuation.Map.fold
      (fun _cont elt map ->
        List.fold_left
          (fun map (_id, var, prim) ->
            match prim with
            | Make_block (_, Mutable, _, args) ->
              (* TODO: remove the mutable constraint, there is no reason to
                 restrict to it. This is only there to test on the mutable
                 cases *)
              if Variable.Set.mem var escaping
              then map
              else Variable.Map.add var args map
            | Make_block (_, (Immutable | Immutable_unique), _, _)
            | Block_load _ | Block_set _ ->
              map)
          map elt.ref_prims_rev)
      source_info.map Variable.Map.empty

  let prims_using_ref ~non_escaping_refs ~dom prim =
    match prim with
    | Make_block _ -> Variable.Set.empty
    | Block_set (_, _, block, _, _) | Block_load (_, _, block, _) ->
      let block =
        match Variable.Map.find block dom with
        | exception Not_found -> block
        | block -> block
      in
      if Variable.Map.mem block non_escaping_refs
      then Variable.Set.singleton block
      else Variable.Set.empty

  let continuations_using_refs ~non_escaping_refs ~dom ~source_info =
    Continuation.Map.mapi
      (fun _cont elt ->
        let used =
          List.fold_left
            (fun used_ref (_id, _var, prim) ->
              Variable.Set.union used_ref
                (prims_using_ref ~non_escaping_refs ~dom prim))
            Variable.Set.empty elt.ref_prims_rev
        in
        if not (Variable.Set.is_empty used)
        then
          Format.printf "Cont using ref %a %a@." Continuation.print _cont
            Variable.Set.print used;
        used)
      source_info.map

  let continuations_defining_refs ~non_escaping_refs ~source_info =
    Continuation.Map.mapi
      (fun _cont elt ->
        let defined =
          List.fold_left
            (fun used_ref (_id, var, _prim) ->
              if Variable.Map.mem var non_escaping_refs
              then Variable.Set.add var used_ref
              else used_ref)
            Variable.Set.empty elt.ref_prims_rev
        in
        if not (Variable.Set.is_empty defined)
        then
          Format.printf "Cont defining ref %a %a@." Continuation.print _cont
            Variable.Set.print defined;
        defined)
      source_info.map

  module Fold_prims = struct
    type rewrite =
      | Remove
      | Binding of
          { var : Variable.t;
            bound_to : Simple.t
          }

    type env =
      { bindings : Simple.t Numeric_types.Int.Map.t Variable.Map.t;
        (* non escaping references bindings *)
        rewrites : rewrite Named_rewrite_id.Map.t
      }

    let list_to_int_map l =
      let _, map =
        List.fold_left
          (fun (i, fields) elt ->
            let fields = Numeric_types.Int.Map.add i elt fields in
            i + 1, fields)
          (0, Numeric_types.Int.Map.empty)
          l
      in
      map

    let apply_prim ~dom env rewrite_id var (prim : ref_prim) =
      match prim with
      | Block_load (_kind, _mut, block, field) -> (
        match Variable.Map.find block dom with
        | exception Not_found -> env
        | block -> (
          match Variable.Map.find block env.bindings with
          | exception Not_found -> env
          | fields ->
            let bound_to = Numeric_types.Int.Map.find field fields in
            let rewrite = Binding { var; bound_to } in
            { env with
              rewrites =
                Named_rewrite_id.Map.add rewrite_id rewrite env.rewrites
            }))
      | Block_set (_, _, block, field, value) -> (
        match Variable.Map.find block dom with
        | exception Not_found -> env
        | block -> (
          match Variable.Map.find block env.bindings with
          | exception Not_found -> env
          | fields ->
            let rewrite = Remove in
            let fields = Numeric_types.Int.Map.add field value fields in
            { bindings = Variable.Map.add block fields env.bindings;
              rewrites =
                Named_rewrite_id.Map.add rewrite_id rewrite env.rewrites
            }))
      | Make_block (_, _, _, values) ->
        let rewrite = Remove in
        let fields = list_to_int_map values in
        { bindings = Variable.Map.add var fields env.bindings;
          rewrites = Named_rewrite_id.Map.add rewrite_id rewrite env.rewrites
        }

    let init_env ~(non_escaping_refs : Simple.t list Variable.Map.t)
        ~(refs_needed : Variable.Set.t) ~rewrites =
      let env, params =
        Variable.Set.fold
          (fun ref_needed (env, params) ->
            let arity =
              List.length (Variable.Map.find ref_needed non_escaping_refs)
            in
            let ref_params =
              List.init arity (fun i -> Variable.create (string_of_int i))
            in
            let env =
              let fields = list_to_int_map (List.map Simple.var ref_params) in
              { env with
                bindings = Variable.Map.add ref_needed fields env.bindings
              }
            in
            env, ref_params @ params)
          refs_needed
          ({ bindings = Variable.Map.empty; rewrites }, [])
      in
      env, params

    let append_int_map i1 i2 =
      if Numeric_types.Int.Map.is_empty i1
      then i2
      else
        let max, _ = Numeric_types.Int.Map.max_binding i1 in
        let shifted_i2 =
          Numeric_types.Int.Map.map_keys (fun i -> i + max + 1) i2
        in
        Numeric_types.Int.Map.disjoint_union i1 shifted_i2

    let do_stuff ~(non_escaping_refs : Simple.t list Variable.Map.t)
        ~continuations_with_live_ref ~dom ~source_info =
      let rewrites = ref Named_rewrite_id.Map.empty in
      Continuation.Map.mapi
        (fun cont (refs_needed : Variable.Set.t) ->
          let elt = Continuation.Map.find cont source_info.map in
          let env, extra_ref_params =
            init_env ~non_escaping_refs ~refs_needed ~rewrites:!rewrites
          in
          let env =
            List.fold_left
              (fun env (rewrite_id, var, prim) ->
                apply_prim ~dom env rewrite_id var prim)
              env
              (List.rev elt.ref_prims_rev)
          in
          rewrites := env.rewrites;
          let refs_params_to_add cont rewrites =
            Apply_cont_rewrite_id.Map.map
              (fun _args ->
                let refs_needed =
                  Continuation.Map.find cont continuations_with_live_ref
                in
                let extra_args =
                  Variable.Set.fold
                    (fun ref_needed extra_args ->
                      let args = Variable.Map.find ref_needed env.bindings in
                      append_int_map extra_args args)
                    refs_needed Numeric_types.Int.Map.empty
                in
                let extra_args =
                  Numeric_types.Int.Map.map
                    (fun s -> Cont_arg.Simple s)
                    extra_args
                in
                extra_args)
              rewrites
          in
          let new_apply_cont_args =
            Continuation.Map.mapi refs_params_to_add elt.apply_cont_args
          in
          extra_ref_params, new_apply_cont_args)
        continuations_with_live_ref
  end

  let continuations_with_live_ref ~non_escaping_refs ~dom ~source_info ~callers
      =
    let continuations_defining_refs =
      continuations_defining_refs ~non_escaping_refs ~source_info
    in
    let continuations_using_refs =
      continuations_using_refs ~non_escaping_refs ~dom ~source_info
    in
    (* TODO factorise fixpoint code *)
    let q_is_empty, pop, push =
      let q = Queue.create () in
      let q_s = ref Continuation.Set.empty in
      ( (fun () -> Queue.is_empty q),
        (fun () ->
          let k = Queue.pop q in
          q_s := Continuation.Set.remove k !q_s;
          k),
        fun k ->
          if not (Continuation.Set.mem k !q_s)
          then (
            Queue.add k q;
            q_s := Continuation.Set.add k !q_s) )
    in
    let () =
      Continuation.Map.iter
        (fun cont used -> if not (Variable.Set.is_empty used) then push cont)
        continuations_using_refs
    in
    let res = ref continuations_using_refs in
    while not (q_is_empty ()) do
      let k = pop () in
      (* let elt = Continuation.Map.find k source_info.map in *)
      let used_refs = Continuation.Map.find k !res in
      let callers =
        match Continuation.Map.find k callers with
        | exception Not_found ->
          Misc.fatal_errorf "Callers not found for: %a" Continuation.print k
        | callers -> callers
      in
      Continuation.Set.iter
        (fun caller ->
          let defined_refs =
            Continuation.Map.find caller continuations_defining_refs
          in
          let old_using_refs = Continuation.Map.find caller !res in
          let new_using_refs =
            Variable.Set.union old_using_refs
              (Variable.Set.diff used_refs defined_refs)
          in
          if not (Variable.Set.equal old_using_refs new_using_refs)
          then (
            res := Continuation.Map.add caller new_using_refs !res;
            push caller))
        callers
    done;
    !res

  (* TODO: For all continuations with live ref, add parameters for every field
     of every live ref.

     for all continuations, fold over the ref_prims (after list rev) to
     propagate the names of the fields at each block_set and record aliases for
     block_load.

     for evey apply cont to those continuations, add the corresponding arguments
     using the last names of the fields. *)

  let create ~(dom : Dominator_graph.result) ~(dom_graph : Dominator_graph.t)
      ~(source_info : source_info)
      ~(callers : Continuation.Set.t Continuation.Map.t) : t =
    let escaping = escaping ~dom ~dom_graph ~source_info in
    let non_escaping_refs = non_escaping_makeblocks ~escaping ~source_info in
    if not (Variable.Map.is_empty non_escaping_refs)
    then
      Format.printf "Non escaping makeblocks %a@."
        (Variable.Map.print Simple.List.print)
        non_escaping_refs;
    let continuations_with_live_ref =
      continuations_with_live_ref ~non_escaping_refs ~dom ~source_info ~callers
    in
    Format.printf "@[<hov 2>Cont using refs:@ %a@]@."
      (Continuation.Map.print Variable.Set.print)
      continuations_with_live_ref;
    let toplevel_used =
      Continuation.Map.find source_info.dummy_toplevel_cont
        continuations_with_live_ref
    in
    if not (Variable.Set.is_empty toplevel_used)
    then
      Misc.fatal_errorf
        "Toplevel continuation cannot have needed extra argument for ref: %a@."
        Variable.Set.print toplevel_used;
    let extra_ref_params_and_args =
      Fold_prims.do_stuff ~dom ~source_info ~continuations_with_live_ref
        ~non_escaping_refs
    in
    { extra_ref_params_and_args;
      non_escaping_makeblock = non_escaping_refs;
      continuations_with_live_ref
    }

  let pp_node { non_escaping_makeblock = _; continuations_with_live_ref; _ } ppf
      cont =
    match Continuation.Map.find cont continuations_with_live_ref with
    | exception Not_found -> ()
    | live_refs -> Format.fprintf ppf " %a" Variable.Set.print live_refs
end

module Control_flow_graph = struct
  type t =
    { dummy_toplevel_cont : Continuation.t;
      callers : Continuation.Set.t Continuation.Map.t;
      parents : Continuation.t Continuation.Map.t;
      children : Continuation.Set.t Continuation.Map.t
    }

  let create ~dummy_toplevel_cont { map; _ } =
    let parents =
      Continuation.Map.filter_map
        (fun _ (elt : elt) -> elt.parent_continuation)
        map
    in
    let children =
      Continuation.Map.fold
        (fun k parent acc ->
          Continuation.Map.update parent
            (function
              | None -> Some (Continuation.Set.singleton k)
              | Some set -> Some (Continuation.Set.add k set))
            acc)
        parents Continuation.Map.empty
    in
    let callers =
      Continuation.Map.fold
        (fun caller (elt : elt) acc ->
          let acc =
            Continuation.Map.merge
              (fun _callee acc args ->
                match acc, args with
                | None, None -> assert false
                | Some set, None -> Some set
                | None, Some _ -> Some (Continuation.Set.singleton caller)
                | Some set, Some _ -> Some (Continuation.Set.add caller set))
              acc elt.apply_cont_args
          in
          acc)
        map
        (Continuation.Map.singleton dummy_toplevel_cont Continuation.Set.empty)
    in
    { dummy_toplevel_cont; callers; parents; children }

  (* This does not need to be tail-rec as other parts of flambda2 are already
     not tail-rec in the number of nested continuations. *)
  let map_fold_on_children { children; dummy_toplevel_cont; _ } f acc =
    let rec aux k acc =
      let acc, to_add = f k acc in
      let map = Continuation.Map.singleton k to_add in
      match Continuation.Map.find k children with
      | exception Not_found -> map
      | s ->
        Continuation.Set.fold
          (fun child map -> Continuation.Map.disjoint_union map (aux child acc))
          s map
    in
    aux dummy_toplevel_cont acc

  let compute_available_variables ~(source_info : source_info) t =
    map_fold_on_children t
      (fun k acc ->
        let elt = Continuation.Map.find k source_info.map in
        let extra_vars =
          match Continuation.Map.find k source_info.extra with
          | exception Not_found -> Variable.Set.empty
          | epa ->
            let extra_params =
              Continuation_extra_params_and_args.extra_params epa
            in
            Bound_parameters.var_set extra_params
        in
        let acc =
          Variable.Set.union
            (Variable.Set.union acc (Bound_parameters.var_set elt.params))
            extra_vars
        in
        acc, acc)
      Variable.Set.empty

  let compute_transitive_parents t =
    map_fold_on_children t
      (fun k acc ->
        let acc = Continuation.Set.add k acc in
        acc, acc)
      Continuation.Set.empty

  let compute_added_extra_args added_extra_args t =
    map_fold_on_children t
      (fun k available ->
        ( Variable.Set.union (Continuation.Map.find k added_extra_args) available,
          available ))
      Variable.Set.empty

  let compute_continuation_extra_args_for_aliases ~required_names
      ~(source_info : source_info) doms t :
      continuation_parameters Continuation.Map.t =
    let available_variables = compute_available_variables ~source_info t in
    let transitive_parents = compute_transitive_parents t in
    let remove_vars_in_scope_of k var_set =
      let elt : elt = Continuation.Map.find k source_info.map in
      let res =
        Variable.Set.diff var_set (Continuation.Map.find k available_variables)
      in
      Variable.Set.diff res elt.defined
    in
    let q_is_empty, pop, push =
      let q = Queue.create () in
      let q_s = ref Continuation.Set.empty in
      ( (fun () -> Queue.is_empty q),
        (fun () ->
          let k = Queue.pop q in
          q_s := Continuation.Set.remove k !q_s;
          k),
        fun k ->
          if not (Continuation.Set.mem k !q_s)
          then (
            Queue.add k q;
            q_s := Continuation.Set.add k !q_s) )
    in
    let init =
      Continuation.Map.mapi
        (fun k elt ->
          let s =
            List.fold_left
              (fun acc param ->
                let dom =
                  match Variable.Map.find param doms with
                  | exception Not_found ->
                    if Name.Set.mem (Name.var param) required_names
                    then
                      Misc.fatal_errorf "Dom not found for: %a@." Variable.print
                        param
                    else param
                  | dom -> dom
                in
                if Variable.equal param dom
                then acc
                else Variable.Set.add dom acc)
              Variable.Set.empty
              (Bound_parameters.vars elt.params)
          in
          let s = remove_vars_in_scope_of k s in
          if not (Variable.Set.is_empty s) then push k;
          s)
        source_info.map
    in
    let res = ref init in
    while not (q_is_empty ()) do
      let k = pop () in
      let elt = Continuation.Map.find k source_info.map in
      let aliases_needed = Continuation.Map.find k !res in
      let callers =
        match Continuation.Map.find k t.callers with
        | exception Not_found ->
          Misc.fatal_errorf "Callers not found for: %a" Continuation.print k
        | callers -> callers
      in
      let callers =
        if not elt.recursive
        then callers
        else
          Continuation.Set.filter
            (fun caller ->
              not
                (Continuation.Set.mem k
                   (Continuation.Map.find caller transitive_parents)))
            callers
      in
      Continuation.Set.iter
        (fun caller ->
          let old_aliases_needed = Continuation.Map.find caller !res in
          let new_aliases_needed =
            Variable.Set.union old_aliases_needed
              (remove_vars_in_scope_of caller aliases_needed)
          in
          if not (Variable.Set.equal old_aliases_needed new_aliases_needed)
          then (
            res := Continuation.Map.add caller new_aliases_needed !res;
            push caller))
        callers
    done;
    let extra_args_for_toplevel_cont =
      Continuation.Map.find t.dummy_toplevel_cont !res
    in
    if not (Variable.Set.is_empty extra_args_for_toplevel_cont)
    then
      Format.eprintf
        "ERROR:@\nToplevel continuation cannot have needed extra argument: %a@."
        Variable.Set.print extra_args_for_toplevel_cont;
    let added_extra_args = !res in
    let available_added_extra_args =
      compute_added_extra_args added_extra_args t
    in
    Continuation.Map.mapi
      (fun k aliases_needed ->
        let available = Continuation.Map.find k available_added_extra_args in
        let extra_args_for_aliases =
          Variable.Set.diff aliases_needed available
        in
        let elt = Continuation.Map.find k source_info.map in
        let exception_handler_first_param : Variable.t option =
          if elt.is_exn_handler
          then
            match Bound_parameters.to_list elt.params with
            | [] ->
              Misc.fatal_errorf
                "exception handler continuation %a must have at least one \
                 parameter"
                Continuation.print k
            | first :: _ -> Some (Bound_parameter.var first)
          else None
        in
        (* For exception continuations the first parameter cannot be removed, so
           instead of rewriting the parameter to its dominator, we instead
           rewrite every alias to the exception parameter *)
        let extra_args_for_aliases, exception_handler_first_param_aliased =
          match exception_handler_first_param with
          | None -> extra_args_for_aliases, None
          | Some exception_param -> (
            match Variable.Map.find exception_param doms with
            | exception Not_found -> extra_args_for_aliases, None
            | alias ->
              if Variable.equal exception_param alias
              then extra_args_for_aliases, None
              else
                ( Variable.Set.remove alias extra_args_for_aliases,
                  Some (alias, exception_param) ))
        in
        let removed_aliased_params_and_extra_params, lets_to_introduce =
          List.fold_left
            (fun (removed, lets_to_introduce) param ->
              match Variable.Map.find param doms with
              | exception Not_found -> removed, lets_to_introduce
              | alias -> (
                if Variable.equal param alias
                then removed, lets_to_introduce
                else
                  match exception_handler_first_param_aliased with
                  | None ->
                    let removed = Variable.Set.add param removed in
                    let lets_to_introduce =
                      Variable.Map.add param alias lets_to_introduce
                    in
                    removed, lets_to_introduce
                  | Some (aliased_to, exception_param) ->
                    let is_first_exception_param =
                      Variable.equal exception_param param
                    in
                    if is_first_exception_param
                    then removed, lets_to_introduce
                    else
                      let alias =
                        if Variable.equal alias aliased_to
                        then exception_param
                        else alias
                      in
                      let removed = Variable.Set.add param removed in
                      let lets_to_introduce =
                        Variable.Map.add param alias lets_to_introduce
                      in
                      removed, lets_to_introduce))
            (Variable.Set.empty, Variable.Map.empty)
            (Bound_parameters.vars elt.params)
        in
        let recursive_continuation_wrapper =
          if elt.recursive && not (Variable.Set.is_empty extra_args_for_aliases)
          then Wrapper_needed
          else No_wrapper
        in
        { extra_args_for_aliases;
          removed_aliased_params_and_extra_params;
          lets_to_introduce;
          recursive_continuation_wrapper
        })
      added_extra_args

  module Dot = struct
    let node_id ~ctx ppf (cont : Continuation.t) =
      Format.fprintf ppf "node_%d_%d" ctx (cont :> int)

    let node ?(extra_args = Variable.Set.empty) ?(info = "") ~df ~pp_node ~ctx
        () ppf cont =
      let params, shape =
        match Continuation.Map.find cont df.map with
        | exception Not_found -> "[ none ]", ""
        | elt ->
          let params =
            Format.asprintf "[%a]"
              (Format.pp_print_list
                 ~pp_sep:(fun ppf () -> Format.fprintf ppf ", ")
                 Variable.print)
              (Bound_parameters.vars elt.params)
          in
          let shape = if elt.recursive then "shape=record" else "" in
          params, shape
      in
      Format.fprintf ppf "%a [label=\"%a %s %s%s\" %s %s];@\n" (node_id ~ctx)
        cont Continuation.print cont params
        (String.map
           (function '{' -> '[' | '}' -> ']' | c -> c)
           (Format.asprintf "%a" Variable.Set.print extra_args))
        (String.map
           (function '{' -> '[' | '}' -> ']' | c -> c)
           (Format.asprintf "%a" pp_node cont))
        shape info

    let nodes ~df ~ctx ~return_continuation ~exn_continuation
        ~continuation_parameters ~pp_node ppf cont_map =
      Continuation.Set.iter
        (fun cont ->
          let extra_args =
            Option.map
              (fun continuation_parameters ->
                continuation_parameters.extra_args_for_aliases)
              (Continuation.Map.find_opt cont continuation_parameters)
          in
          let info =
            if Continuation.equal return_continuation cont
            then "color=blue"
            else if Continuation.equal exn_continuation cont
            then "color=red"
            else ""
          in
          node ?extra_args ~df ~ctx ~info ~pp_node () ppf cont)
        cont_map

    let edge ~ctx ~color ppf src dst =
      Format.fprintf ppf "%a -> %a [color=\"%s\"];@\n" (node_id ~ctx) dst
        (node_id ~ctx) src color

    let edges ~ctx ~color ppf edge_map =
      Continuation.Map.iter
        (fun src dst_set ->
          Continuation.Set.iter
            (fun dst -> edge ~ctx ~color ppf src dst)
            dst_set)
        edge_map

    let edges' ~ctx ~color ppf edge_map =
      Continuation.Map.iter
        (fun src dst -> edge ~ctx ~color ppf src dst)
        edge_map

    let print ~ctx ~df ~print_name ppf ~return_continuation ~exn_continuation
        ?(pp_node = fun _ppf _cont -> ()) ~continuation_parameters (t : t) =
      let dummy_toplevel_cont = t.dummy_toplevel_cont in
      let all_conts =
        Continuation.Map.fold
          (fun cont callers acc ->
            Continuation.Set.add cont (Continuation.Set.union callers acc))
          t.callers
          (Continuation.Set.of_list
             [dummy_toplevel_cont; return_continuation; exn_continuation])
      in
      let all_conts =
        Continuation.Map.fold
          (fun cont _parent acc -> Continuation.Set.add cont acc)
          t.parents all_conts
      in
      Flambda_colours.without_colours ~f:(fun () ->
          Format.fprintf ppf
            "subgraph cluster_%d { label=\"%s\";@\n%a%a@\n%a@\n%a@\n}@." ctx
            print_name
            (node ~df ~ctx ~pp_node ())
            dummy_toplevel_cont
            (nodes ~df ~return_continuation ~exn_continuation ~ctx
               ~continuation_parameters ~pp_node)
            all_conts
            (edges' ~ctx ~color:"green")
            t.parents
            (edges ~ctx ~color:"black")
            t.callers)
  end
end

(* Analysis *)
(* ******** *)

let r = ref ~-1

let dominator_graph_ppf =
  lazy
    (match Sys.getenv_opt "DOM_GRAPH" with
    | None -> None
    | Some filename ->
      let ch = open_out filename in
      let ppf = Format.formatter_of_out_channel ch in
      Format.fprintf ppf "digraph g {@\n";
      at_exit (fun () ->
          Format.fprintf ppf "@\n}@.";
          close_out ch);
      Some ppf)

let control_flow_graph_ppf =
  lazy
    (match Sys.getenv_opt "FLOW_GRAPH" with
    | None -> None
    | Some filename ->
      let ch = open_out filename in
      let ppf = Format.formatter_of_out_channel ch in
      Format.fprintf ppf "digraph g {@\n";
      at_exit (fun () ->
          Format.fprintf ppf "@\n}@.";
          close_out ch);
      Some ppf)

let debug = Sys.getenv_opt "DF" <> None

let analyze ?print_name ~return_continuation ~exn_continuation
    ~code_age_relation ~used_value_slots t : result =
  Profile.record_call ~accumulate:true "data_flow" (fun () ->
      if debug then Format.eprintf "PRESOURCE:@\n%a@\n@." print t;
      let ({ stack; map; extra = _; dummy_toplevel_cont } as t) =
        extend_args_with_extra_args t
      in
      assert (stack = []);
      assert (
        not
          (Continuation.name dummy_toplevel_cont
          = wrong_dummy_toplevel_cont_name));
      if debug then Format.eprintf "SOURCE:@\n%a@\n@." print t;
      (* Dead variable analysis *)
      let deps =
        Dependency_graph.create map ~return_continuation ~exn_continuation
          ~code_age_relation ~used_value_slots
      in
      if debug
      then Format.eprintf "/// graph@\n%a@\n@." Dependency_graph._print deps;
      let dead_variable_result = Dependency_graph.required_names deps in
      (* Aliases analysis *)
      let dom_graph =
        Dominator_graph.create map ~return_continuation ~exn_continuation
          ~required_names:dead_variable_result.required_names
      in
      let aliases = Dominator_graph.dominator_analysis dom_graph in
      let aliases_kind = Dominator_graph.aliases_kind dom_graph aliases in
      (match print_name with
      | None -> ()
      | Some print_name ->
        Option.iter
          (fun ppf ->
            incr r;
            Dominator_graph.Dot.print ~print_name ~ctx:!r ~doms:aliases ppf
              dom_graph)
          (Lazy.force dominator_graph_ppf));
      let control = Control_flow_graph.create ~dummy_toplevel_cont t in
      let escaping =
        Non_escaping_references.create ~dom:aliases ~dom_graph ~source_info:t
          ~callers:control.callers
      in
      let pp_node = Non_escaping_references.pp_node escaping in
      let continuation_parameters =
        Control_flow_graph.compute_continuation_extra_args_for_aliases
          ~source_info:t aliases control
          ~required_names:dead_variable_result.required_names
      in
      (match print_name with
      | None -> ()
      | Some print_name ->
        Option.iter
          (fun ppf ->
            incr r;
            Control_flow_graph.Dot.print ~df:t ~print_name ~ctx:!r ppf
              ~return_continuation ~exn_continuation ~continuation_parameters
              ~pp_node control)
          (Lazy.force control_flow_graph_ppf));
      (* Return *)
      let result =
        { dead_variable_result;
          continuation_param_aliases = { aliases_kind; continuation_parameters }
        }
      in
      if debug then Format.eprintf "/// result@\n%a@\n@." _print_result result;
      result)
