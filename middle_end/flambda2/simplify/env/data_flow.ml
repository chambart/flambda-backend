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

[@@@ocaml.warning "+a-4-30-40-41-42"]

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

(* CR-someday chambart/gbury: get rid of Name_occurences everywhere, this is not
   small while we need only the names

   mshinwell: in practice I'm not sure this will make any difference *)
type elt =
  { continuation : Continuation.t;
    recursive : bool;
    params : Bound_parameters.t;
    used_in_handler : Name_occurrences.t;
    apply_result_conts : Continuation.Set.t;
    bindings : Name_occurrences.t Name.Map.t;
    code_ids : Name_occurrences.t Code_id.Map.t;
    value_slots : Name_occurrences.t Name.Map.t Value_slot.Map.t;
    apply_cont_args : Simple.Set.t Numeric_types.Int.Map.t Continuation.Map.t;
    rewrite_ids : Apply_cont_rewrite_id.Set.t Continuation.Map.t;
    inside : Continuation.t option
  }

type t =
  { stack : elt list;
    map : elt Continuation.Map.t;
    extra : Continuation_extra_params_and_args.t Continuation.Map.t;
    dummy_toplevel_cont : Continuation.t option;
    kinds : Flambda_kind.With_subkind.t Variable.Map.t
  }

type result =
  { required_names : Name.Set.t;
    reachable_code_ids : Reachable_code_ids.t;
    aliases : Variable.t Variable.Map.t;
    required_new_args : Bound_parameters.t Continuation.Map.t
  }

(* Print *)
(* ***** *)

let print_elt ppf
    { continuation;
      recursive;
      params;
      used_in_handler;
      apply_result_conts;
      bindings;
      code_ids;
      value_slots;
      apply_cont_args;
      rewrite_ids;
      inside
    } =
  Format.fprintf ppf
    "@[<hov 1>(@[<hov 1>(continuation %a)@]@ @[<hov 1>(recursive %b)@]@ @[<hov \
     1>(params %a)@]@ @[<hov 1>(used_in_handler %a)@]@ @[<hov \
     1>(apply_result_conts %a)@]@ @[<hov 1>(bindings %a)@]@ @[<hov 1>(code_ids \
     %a)@]@ @[<hov 1>(value_slots %a)@]@ @[<hov 1>(apply_cont_args %a)@])@ \
     @[<hov 1>(rewrite_ids %a)@])@ @[<hov 1>(inside %a)@])@]"
    Continuation.print continuation recursive Bound_parameters.print params
    Name_occurrences.print used_in_handler Continuation.Set.print
    apply_result_conts
    (Name.Map.print Name_occurrences.print)
    bindings
    (Code_id.Map.print Name_occurrences.print)
    code_ids
    (Value_slot.Map.print (Name.Map.print Name_occurrences.print))
    value_slots
    (Continuation.Map.print (Numeric_types.Int.Map.print Simple.Set.print))
    apply_cont_args
    (Continuation.Map.print Apply_cont_rewrite_id.Set.print)
    rewrite_ids
    (Format.pp_print_option Continuation.print)
    inside

let print_stack ppf stack =
  Format.fprintf ppf "@[<v 1>(%a)@]"
    (Format.pp_print_list print_elt ~pp_sep:Format.pp_print_space)
    stack

let print_map ppf map = Continuation.Map.print print_elt ppf map

let print_extra ppf extra =
  Continuation.Map.print Continuation_extra_params_and_args.print ppf extra

let [@ocamlformat "disable"] print ppf
  { stack; map; extra; dummy_toplevel_cont = _; kinds = _ } =
  Format.fprintf ppf
    "@[<hov 1>(\
      @[<hov 1>(stack %a)@]@ \
      @[<hov 1>(map %a)@]@ \
      @[<hov 1>(extra %a)@]\
      )@]"
    print_stack stack
    print_map map
    print_extra extra

let [@ocamlformat "disable"] _print_result ppf
  { required_names; reachable_code_ids; aliases; required_new_args } =
  Format.fprintf ppf
    "@[<hov 1>(\
      @[<hov 1>(required_names@ %a)@]@ \
      @[<hov 1>(reachable_code_ids@ %a)@]@ \
      @[<hov 1>(aliases@ %a)@]@ \
      @[<hov 1>(required_new_args@ %a)@]\
      )@]"
    Name.Set.print required_names Reachable_code_ids.print reachable_code_ids
    (Variable.Map.print Variable.print) aliases
    (Continuation.Map.print Bound_parameters.print) required_new_args

(* Creation *)
(* ******** *)

let empty =
  { stack = [];
    map = Continuation.Map.empty;
    extra = Continuation.Map.empty;
    dummy_toplevel_cont = None;
    kinds = Variable.Map.empty
  }

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

let enter_continuation continuation ~recursive params t =
  let inside =
    match t.stack with [] -> None | inside :: _ -> Some inside.continuation
  in
  let elt =
    { continuation;
      recursive;
      params;
      bindings = Name.Map.empty;
      code_ids = Code_id.Map.empty;
      value_slots = Value_slot.Map.empty;
      used_in_handler = Name_occurrences.empty;
      apply_cont_args = Continuation.Map.empty;
      apply_result_conts = Continuation.Set.empty;
      rewrite_ids = Continuation.Map.empty;
      inside
    }
  in
  let kinds =
    List.fold_left
      (fun kinds bp ->
        Variable.Map.add (Bound_parameter.var bp) (Bound_parameter.kind bp)
          kinds)
      t.kinds
      (Bound_parameters.to_list params)
  in
  { t with kinds; stack = elt :: t.stack }

let init_toplevel continuation params _t =
  { (enter_continuation continuation ~recursive:false params empty) with
    dummy_toplevel_cont = Some continuation
  }

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

let insert_kind var kind t =
  { t with kinds = Variable.Map.add var kind t.kinds }

let record_var_binding var kind name_occurrences ~generate_phantom_lets t =
  insert_kind var kind
  @@ update_top_of_stack ~t ~f:(fun elt ->
         let bindings =
           Name.Map.update (Name.var var)
             (function
               | None -> Some name_occurrences
               | Some _ ->
                 Misc.fatal_errorf
                   "The following variable has been bound twice: %a"
                   Variable.print var)
             elt.bindings
         in
         let used_in_handler =
           if Variable.user_visible var && generate_phantom_lets
           then
             Name_occurrences.add_variable elt.used_in_handler var
               Name_mode.phantom
           else elt.used_in_handler
         in
         { elt with bindings; used_in_handler })

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

let record_cont_use k rewrite_id t =
  update_top_of_stack ~t ~f:(fun elt ->
      let rewrite_ids =
        Continuation.Map.update k
          (fun rewrite_ids ->
            let rewrite_ids =
              match rewrite_ids with
              | None -> Apply_cont_rewrite_id.Set.singleton rewrite_id
              | Some set -> Apply_cont_rewrite_id.Set.add rewrite_id set
            in
            Some rewrite_ids)
          elt.rewrite_ids
      in
      { elt with rewrite_ids })

let add_apply_result_cont k t =
  update_top_of_stack ~t ~f:(fun elt ->
      let apply_result_conts = Continuation.Set.add k elt.apply_result_conts in
      { elt with apply_result_conts })

let add_apply_cont_args cont args t =
  update_top_of_stack ~t ~f:(fun elt ->
      let apply_cont_args =
        Continuation.Map.update cont
          (fun map_opt ->
            let map =
              Option.value ~default:Numeric_types.Int.Map.empty map_opt
            in
            let map, _ =
              List.fold_left
                (fun (map, i) arg ->
                  let map =
                    Numeric_types.Int.Map.update i
                      (fun old_opt ->
                        let old =
                          Option.value ~default:Simple.Set.empty old_opt
                        in
                        Some (Simple.Set.add arg old))
                      map
                  in
                  map, i + 1)
                (map, 0) args
            in
            Some map)
          elt.apply_cont_args
      in
      { elt with apply_cont_args })

(* Control flow *)
(* ************ *)

module Control_flow = struct
  type c =
    { prev : Continuation.Set.t Continuation.Map.t;
      dummy_toplevel_cont : Continuation.t;
      return_continuation : Continuation.t;
      exn_continuation : Continuation.t;
      recursive_continuations : Continuation.Set.t;
      contains : Continuation.Set.t Continuation.Map.t;
      end_with_func_call : Continuation.Set.t
          (* introduced_continuations : Continuation.Set.t; *)
    }

  let create ~return_continuation ~exn_continuation (t : t) =
    let dummy_toplevel_cont =
      match t.dummy_toplevel_cont with
      | None -> assert false
      | Some dummy_toplevel_cont -> dummy_toplevel_cont
    in
    let add (prev : Continuation.Set.t Continuation.Map.t) ~from ~to_ =
      let set =
        match Continuation.Map.find_opt to_ prev with
        | None -> Continuation.Set.singleton from
        | Some set -> Continuation.Set.add from set
      in
      Continuation.Map.add to_ set prev
    in
    let prev =
      Continuation.Map.fold
        (fun from (elt : elt) (prev : Continuation.Set.t Continuation.Map.t) ->
          let prev =
            Continuation.Map.fold
              (fun to_ _ prev -> add prev ~from ~to_)
              elt.apply_cont_args prev
          in
          Continuation.Set.fold
            (fun to_ prev -> add prev ~from ~to_)
            elt.apply_result_conts prev)
        t.map Continuation.Map.empty
    in
    let end_with_func_call =
      Continuation.Map.fold
        (fun from (elt : elt) set ->
          if Continuation.Set.is_empty elt.apply_result_conts
          then set
          else Continuation.Set.add from set)
        t.map Continuation.Set.empty
    in
    let recursive_continuations =
      Continuation.Map.fold
        (fun cont (elt : elt) set ->
          if elt.recursive then Continuation.Set.add cont set else set)
        t.map Continuation.Set.empty
    in
    let contains =
      Continuation.Map.fold
        (fun _ (elt : elt) contains ->
          match elt.inside with
          | None -> contains
          | Some inside ->
            let set =
              match Continuation.Map.find_opt inside contains with
              | None -> Continuation.Set.singleton elt.continuation
              | Some set -> Continuation.Set.add elt.continuation set
            in
            Continuation.Map.add inside set contains)
        t.map Continuation.Map.empty
    in
    { dummy_toplevel_cont;
      prev;
      return_continuation;
      exn_continuation;
      recursive_continuations;
      contains;
      end_with_func_call
    }

  (* module SCC_continuation = Strongly_connected_components.Make
     (Continuation) *)

  let only_variables simples =
    Simple.Set.fold
      (fun s acc ->
        match Simple.must_be_var s with
        | None -> acc
        | Some (var, _) -> Variable.Set.add var acc)
      simples Variable.Set.empty

  let provided elt =
    let bindings =
      Name.Map.fold
        (fun name _ set ->
          Name.pattern_match name
            ~var:(fun v -> Variable.Set.add v set)
            ~symbol:(fun _ -> set))
        elt.bindings Variable.Set.empty
    in
    List.fold_left
      (fun set var -> Variable.Set.add var set)
      bindings
      (Bound_parameters.vars elt.params)

  let make_req t aliases =
    Continuation.Map.filter_map
      (fun _continuation (elt : elt) ->
        let apply_cont_args =
          Continuation.Map.fold
            (fun applied_cont im set ->
              let set =
                Numeric_types.Int.Map.fold
                  (fun _ args set ->
                    Variable.Set.union (only_variables args) set)
                  im set
              in
              let set =
                match
                  ( Continuation.Map.find_opt applied_cont t.extra,
                    Continuation.Map.find_opt applied_cont elt.rewrite_ids )
                with
                | None, Some _ ->
                  (* Format.printf "None, Some %a@." Continuation.print
                   *   _continuation; *)
                  set
                | Some _, None ->
                  (* Format.printf "Some, None %a@." Continuation.print
                   *   _continuation; *)
                  set
                | None, None -> set
                (* | None, _ | _, None -> req *)
                | Some extra, Some rewrite_ids ->
                  (* Format.printf "XXX Some, Some %a@." Continuation.print
                   *   _continuation; *)
                  let set =
                    Apply_cont_rewrite_id.Set.fold
                      (fun rewrite_id set ->
                        let extra_args =
                          match
                            Apply_cont_rewrite_id.Map.find_opt rewrite_id
                              extra.extra_args
                          with
                          | None -> []
                          | Some extra_args -> extra_args
                        in
                        List.fold_left
                          (fun set (extra_arg : EPA.Extra_arg.t) ->
                            match extra_arg with
                            | Already_in_scope s -> begin
                              match Simple.must_be_var s with
                              | None -> set
                              | Some (var, _) -> Variable.Set.add var set
                            end
                            | New_let_binding _
                            | New_let_binding_with_named_args _ ->
                              (* We dont't rewrite let bindings yet so those
                                 dependencies don't need to be accounted for YET
                                 XXX TODO XXX *)
                              set)
                          set extra_args)
                      rewrite_ids set
                  in
                  set
              in
              set)
            elt.apply_cont_args Variable.Set.empty
        in

        let req =
          Variable.Set.fold
            (fun var req ->
              match Variable.Map.find_opt var aliases with
              | None -> req
              | Some v -> Variable.Set.add v req)
            apply_cont_args Variable.Set.empty
        in
        if Variable.Set.is_empty req then None else Some req)
      t.map

  let required_vars (t : t) (c : c) (req : Variable.Set.t Continuation.Map.t) =
    (* let components =
       SCC_continuation.connected_components_sorted_from_roots_to_leaf c.prev
       in *)
    let state = ref req in
    let q = Queue.create () in
    Continuation.Map.iter (fun cont _ -> Queue.push cont q) req;
    while not (Queue.is_empty q) do
      let cont = Queue.pop q in
      let req = Continuation.Map.find cont !state in
      let prev =
        if Continuation.equal c.dummy_toplevel_cont cont
        then Continuation.Set.empty
        else
          match Continuation.Map.find_opt cont c.prev with
          | Some p -> p
          | None ->
            Format.eprintf "PREV: %a@. %a@." Continuation.print cont
              (Continuation.Map.print Continuation.Set.print)
              c.prev;
            Format.eprintf "DF:@ %a@." print t;
            assert false
      in
      Continuation.Set.iter
        (fun prev ->
          let provided = provided (Continuation.Map.find prev t.map) in
          let p_req =
            match Continuation.Map.find_opt prev !state with
            | None -> Variable.Set.empty
            | Some s -> s
          in
          let new_req =
            Variable.Set.diff (Variable.Set.union p_req req) provided
          in
          if not (Variable.Set.equal new_req p_req)
          then begin
            state := Continuation.Map.add prev new_req !state;
            Queue.push prev q
          end)
        prev
    done;
    !state

  let remove_scoped (t : t) (c : c) (req : Variable.Set.t Continuation.Map.t) =
    let rec loop elt env req =
      let env =
        List.fold_left
          (fun set var -> Variable.Set.add var set)
          env
          (Bound_parameters.vars elt.params)
      in
      let req, env =
        match Continuation.Map.find_opt elt.continuation req with
        | None -> req, env
        | Some set ->
          let set = Variable.Set.diff set env in
          let req =
            if Variable.Set.is_empty set
            then Continuation.Map.remove elt.continuation req
            else Continuation.Map.add elt.continuation set req
          in
          let env = Variable.Set.union set env in
          req, env
      in
      match Continuation.Map.find_opt elt.continuation c.contains with
      | None -> req
      | Some contained ->
        Continuation.Set.fold
          (fun cont req -> loop (Continuation.Map.find cont t.map) env req)
          contained req
    in
    loop
      (Continuation.Map.find c.dummy_toplevel_cont t.map)
      Variable.Set.empty req

  let insert_new_entry_points (_t : t) (c : c)
      (req : Variable.Set.t Continuation.Map.t) :
      Variable.Set.t Continuation.Map.t * Continuation.t Continuation.Map.t =
    Continuation.Map.fold
      (fun cont cont_req (req, new_conts) ->
        if Continuation.Set.mem cont c.recursive_continuations
        then
          let new_cont =
            Continuation.create ~sort:Normal_or_exn ~name:"rec_entry_point" ()
          in
          let req = Continuation.Map.remove cont req in
          let req = Continuation.Map.add cont cont_req req in
          let new_conts = Continuation.Map.add cont new_cont new_conts in
          req, new_conts
        else req, new_conts)
      req
      (req, Continuation.Map.empty)

  let print_edge ppf (from, to_) =
    Format.fprintf ppf "@[<h 2>%s%i %s %s%i [ label=\"%s\"%s ] ;@]@ "
      (Continuation.name from)
      (Continuation.name_stamp from)
      "->" (Continuation.name to_)
      (Continuation.name_stamp to_)
      "" (* label *) ""
  (* style *)

  let print_call_edge ppf (from, to_) =
    Format.fprintf ppf
      "@[<h 2>%s%i %s %s%i [ label=\"%s\" color=\"blue\"%s ] ;@]@ "
      (Continuation.name from)
      (Continuation.name_stamp from)
      "->" (Continuation.name to_)
      (Continuation.name_stamp to_)
      "" (* label *) ""
  (* style *)

  let print_contains ppf (from, to_) =
    Format.fprintf ppf "@[<h 2>%s%i %s %s%i [ label=\"%s\"%s ] ;@]@ "
      (Continuation.name from)
      (Continuation.name_stamp from)
      "->" (Continuation.name to_)
      (Continuation.name_stamp to_)
      "" (* label *) "color=red"

  let print_vert ppf cont label =
    Format.fprintf ppf
      "@[<h 2>%s%i [ label=\"%s\" shape=\"record\" style=\"rounded, filled\" \
       fillcolor=\"lightblue\"] ;@]@ "
      (Continuation.name cont)
      (Continuation.name_stamp cont)
      label

  let print_rec_vert ppf cont =
    Format.fprintf ppf
      "@[<h 2>%s%i [ style=\"filled\" fillcolor=\"lightyellow\"] ;@]@ "
      (Continuation.name cont)
      (Continuation.name_stamp cont)

  let print_dot ppf c =
    Format.fprintf ppf "@[<hov 2>digraph G {@ ";
    print_vert ppf c.return_continuation "return";
    print_vert ppf c.exn_continuation "exn";
    print_vert ppf c.dummy_toplevel_cont "entry";
    Continuation.Map.iter
      (fun from set ->
        if Continuation.Set.mem from c.recursive_continuations
        then print_rec_vert ppf from;
        if Continuation.Set.mem from c.end_with_func_call
        then
          Continuation.Set.iter (fun to_ -> print_call_edge ppf (from, to_)) set
        else Continuation.Set.iter (fun to_ -> print_edge ppf (from, to_)) set)
      c.prev;
    Continuation.Map.iter
      (fun cont contained ->
        Continuation.Set.iter
          (fun contained -> print_contains ppf (cont, contained))
          contained)
      c.contains;
    Format.fprintf ppf "}@]"
end

(* Alias graph *)
(* *********** *)

module Alias_graph = struct
  type t =
    { var_to_simple : Simple.Set.t Variable.Map.t;
      dummy_escape_var : Variable.t;
      return : Simple.Set.t;
      exn_return : Simple.Set.t
    }

  let empty () =
    { var_to_simple = Variable.Map.empty;
      dummy_escape_var = Variable.create "dummy_escape_var";
      return = Simple.Set.empty;
      exn_return = Simple.Set.empty
    }

  let [@ocamlformat "disable"] _print ppf
    { var_to_simple; return; exn_return; dummy_escape_var = _ } =
    Format.fprintf ppf
      "@[<hov 1>(@[<hov 1>(return@ %a)@]@ \
                 @[<hov 1>(exn_return@ %a)@]@ \
                 @[<hov 1>(var_to_simple@ %a)@])@]"
        Simple.Set.print return
        Simple.Set.print exn_return
        (Variable.Map.print Simple.Set.print) var_to_simple

  let add_dependency ~(src : Variable.t) ~(dst : Simple.Set.t)
      ({ var_to_simple; _ } as t) =
    let var_to_simple =
      Variable.Map.update src
        (function
          | None -> Some dst | Some set -> Some (Simple.Set.union dst set))
        var_to_simple
    in
    { t with var_to_simple }

  let add_continuation_info map ~return_continuation ~exn_continuation _cont
      { apply_cont_args;
        recursive = _;
        apply_result_conts = _;
        used_in_handler = _;
        bindings = _;
        code_ids = _;
        value_slots = _;
        continuation = _;
        params = _;
        rewrite_ids = _;
        inside = _
      } t =
    (* Build the graph of dependencies between continuation parameters and
       arguments. *)
    Continuation.Map.fold
      (fun k args t ->
        if Continuation.equal k return_continuation
        then
          let args = Numeric_types.Int.Map.bindings args in
          match args with
          | [(_idx, arg)] -> { t with return = Simple.Set.union arg t.return }
          | [] | _ :: _ :: _ -> assert false
        else if Continuation.equal k exn_continuation
        then (
          let args = Numeric_types.Int.Map.bindings args in
          match args with
          | [(_idx, arg)] ->
            { t with exn_return = Simple.Set.union arg t.exn_return }
          | [] -> assert false
          | _ :: _ :: _ ->
            Format.eprintf "Cont: %a %a@." Continuation.print k
              Continuation.print exn_continuation;
            Format.eprintf "Args: %i@." (List.length args);
            List.iter
              (fun (_, arg) -> Format.eprintf "  %a@." Simple.Set.print arg)
              args;
            Format.eprintf "############################################@.";
            assert false
          (* t *))
        else
          let params =
            match Continuation.Map.find k map with
            | elt -> Array.of_list (Bound_parameters.vars elt.params)
            | exception Not_found ->
              Misc.fatal_errorf "Continuation not found during Data_flow: %a@."
                Continuation.print k
          in
          Numeric_types.Int.Map.fold
            (fun i arg t ->
              let src = params.(i) in
              add_dependency ~src ~dst:arg t)
            args t)
      apply_cont_args t

  let create ~return_continuation ~exn_continuation map extra =
    let t =
      Continuation.Map.fold
        (add_continuation_info map ~return_continuation ~exn_continuation)
        map (empty ())
    in

    (* Take into account the extra params and args. *)
    let t =
      Continuation.Map.fold
        (fun _ (extra_params_and_args : Continuation_extra_params_and_args.t) t ->
          Apply_cont_rewrite_id.Map.fold
            (fun _ extra_args t ->
              List.fold_left2
                (fun t extra_param extra_arg ->
                  let src = Bound_parameter.var extra_param in
                  match
                    (extra_arg : Continuation_extra_params_and_args.Extra_arg.t)
                  with
                  | Already_in_scope simple ->
                    let dst = Simple.Set.singleton simple in
                    add_dependency ~src ~dst t
                  | New_let_binding (src', _prim) ->
                    add_dependency ~src
                      ~dst:(Simple.Set.singleton (Simple.var src'))
                      t
                  | New_let_binding_with_named_args (src', _prim_gen) ->
                    add_dependency ~src
                      ~dst:(Simple.Set.singleton (Simple.var src'))
                      t)
                t
                (Bound_parameters.to_list extra_params_and_args.extra_params)
                extra_args)
            extra_params_and_args.extra_args t)
        extra t
    in

    t

  module Dom = struct
    module Node = Variable

    type graph =
      { entry : Variable.Set.t;
        links : Variable.Set.t Variable.Map.t
      }

    let [@ocamlformat "disable"] _print ppf { entry; links } =
      Format.fprintf ppf
        "@[<hov 1>(@[<hov 1>(entry@ %a)@]@ \
                   @[<hov 1>(links@ %a)@])@]"
          Variable.Set.print entry
          (Variable.Map.print Variable.Set.print) links

    let [@ocamlformat "disable"] _print_result ppf dom =
      Format.fprintf ppf
        "@[<hov 1>(@[<hov 1>(dominators@ %a)@])@]"
          (Variable.Map.print Variable.Set.print) dom

    let all_variables simples =
      try
        let set =
          Simple.Set.fold
            (fun s acc ->
              match Simple.must_be_var s with
              | None -> raise Exit
              | Some (var, _) -> Variable.Set.add var acc)
            simples Variable.Set.empty
        in
        Some set
      with Exit -> None

    let make_graph (t : t) =
      let g =
        Variable.Map.fold
          (fun node simples g ->
            match all_variables simples with
            | None -> { g with entry = Variable.Set.add node g.entry }
            | Some set ->
              if Variable.Set.mem t.dummy_escape_var set
              then { g with entry = Variable.Set.add node g.entry }
              else { g with links = Variable.Map.add node set g.links })
          t.var_to_simple
          { entry = Variable.Set.empty; links = Variable.Map.empty }
      in
      Variable.Map.fold
        (fun _ prev g ->
          Variable.Set.fold
            (fun v g ->
              if Variable.Map.mem v g.links
              then g
              else { g with entry = Variable.Set.add v g.entry })
            prev g)
        g.links g

    let nodes g =
      Node.Set.union g.entry
        (Node.Map.fold
           (fun k _ set -> Node.Set.add k set)
           g.links Node.Set.empty)

    let init g =
      let nodes = nodes g in
      let init_map = Node.Map.map (fun _ -> nodes) g.links in
      Node.Set.fold
        (fun e map -> Node.Map.add e (Node.Set.singleton e) map)
        g.entry init_map

    let fold_first (first : 'a -> 'b) next (seq : 'a Seq.t) : 'b =
      match seq () with
      | Nil -> invalid_arg "Empty seq"
      | Cons (f, t) -> Seq.fold_left next (first f) t

    let step node pred (state, changed) =
      let new_dom =
        Node.Set.add node
        @@ fold_first
             (fun first -> Node.Map.find first state)
             (fun set elt -> Node.Set.inter set (Node.Map.find elt state))
             (Node.Set.to_seq pred)
      in
      let prev_dom = Node.Map.find node state in
      if Node.Set.equal prev_dom new_dom
      then state, changed
      else Node.Map.add node new_dom state, true

    let dom g =
      let rec loop state =
        let state, changed = Node.Map.fold step g.links (state, false) in
        if changed then loop state else state
      in
      loop (init g)

    let first_dom dom =
      (* TODO memoize *)
      let rec find_root dom node set : Variable.t =
        (* Format.printf "lookup %a %a@." Variable.print node Variable.Set.print
         *   set; *)
        let min = Variable.Set.min_elt set in
        if Variable.equal min node
        then
          let max = Variable.Set.max_elt set in
          if Variable.equal max node
          then node
          else find_root dom max (Variable.Map.find max dom)
        else find_root dom min (Variable.Map.find min dom)
      in
      (* Variable.Map.mapi (find_root dom) dom *)
      Variable.Map.filter_map
        (fun node set ->
          let alias = find_root dom node set in
          if Variable.equal alias node then None else Some alias)
        dom
  end
  (* type result = { aliases : Variable.t Variable.Map.t } *)
end

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
              };
            aliases = Variable.Map.empty;
            required_new_args = Continuation.Map.empty
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
          else begin
            Queue.push src older_queue;
            Code_id.Set.add src older_enqueued
          end
        in
        reachable_code_ids t code_id_queue code_id_enqueued older_queue
          older_enqueued name_queue name_enqueued

    and reachable_older_code_ids t code_id_queue code_id_enqueued older_queue
        older_enqueued name_queue name_enqueued =
      match Queue.take older_queue with
      | exception Queue.Empty ->
        reachable_code_ids t code_id_queue code_id_enqueued older_queue
          older_enqueued name_queue name_enqueued
      | src -> begin
        match
          Code_age_relation.get_older_version_of t.code_age_relation src
        with
        | None ->
          reachable_older_code_ids t code_id_queue code_id_enqueued older_queue
            older_enqueued name_queue name_enqueued
        | Some dst ->
          if Code_id.Set.mem dst older_enqueued
          then begin
            if Code_id.Set.mem dst code_id_enqueued
            then
              reachable_older_code_ids t code_id_queue code_id_enqueued
                older_queue older_enqueued name_queue name_enqueued
            else
              let code_id_enqueued = Code_id.Set.add dst code_id_enqueued in
              Queue.push dst code_id_queue;
              reachable_older_code_ids t code_id_queue code_id_enqueued
                older_queue older_enqueued name_queue name_enqueued
          end
          else
            let older_enqueued = Code_id.Set.add dst older_enqueued in
            reachable_older_code_ids t code_id_queue code_id_enqueued
              older_queue older_enqueued name_queue name_enqueued
      end
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

  let add_name_used ({ unconditionally_used; _ } as t) v =
    let unconditionally_used = Name.Set.add v unconditionally_used in
    { t with unconditionally_used }

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

  let add_var_used t v = add_name_used t (Name.var v)

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

  let add_continuation_info map ~return_continuation ~exn_continuation
      ~used_value_slots _
      { apply_cont_args;
        recursive = _;
        apply_result_conts;
        used_in_handler;
        bindings;
        code_ids;
        value_slots;
        continuation = _;
        params = _;
        rewrite_ids = _;
        inside = _
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
    (* Add the vars of continuation used as function call return as used *)
    let t =
      Continuation.Set.fold
        (fun k t ->
          match Continuation.Map.find k map with
          | elt ->
            List.fold_left add_var_used t (Bound_parameters.vars elt.params)
          | exception Not_found ->
            if Continuation.equal return_continuation k
               || Continuation.equal exn_continuation k
            then t
            else
              Misc.fatal_errorf "Continuation not found during Data_flow: %a@."
                Continuation.print k)
        apply_result_conts t
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
      (fun k (args : Simple.Set.t Numeric_types.Int.Map.t) t ->
        if Continuation.equal return_continuation k
           || Continuation.equal exn_continuation k
        then
          Numeric_types.Int.Map.fold
            (fun _ arg t ->
              Simple.Set.fold
                (fun arg t -> add_name_occurrences (Simple.free_names arg) t)
                arg t)
            args t
        else
          let params =
            match Continuation.Map.find k map with
            | elt -> Array.of_list (Bound_parameters.vars elt.params)
            | exception Not_found ->
              Misc.fatal_errorf "Continuation not found during Data_flow: %a@."
                Continuation.print k
          in
          Numeric_types.Int.Map.fold
            (fun i arg t ->
              (* Note on the direction of the edge:

                 We later do a reachability analysis to compute the transitive
                 closure of the used variables.

                 Therefore an edge from src to dst means: if src is used, then
                 dst is also used.

                 Applied here, this means : if the param of a continuation is
                 used, then any argument provided for that param is also used.
                 The other way wouldn't make much sense. *)
              let src = Name.var params.(i) in
              let name_occurrence =
                Simple.Set.fold
                  (fun arg t ->
                    Name_occurrences.union t (Simple.free_names arg))
                  arg Name_occurrences.empty
              in
              Name_occurrences.fold_names name_occurrence ~init:t
                ~f:(fun t dst -> add_dependency ~src ~dst t))
            args t)
      apply_cont_args t

  let create ~return_continuation ~exn_continuation ~code_age_relation
      ~used_value_slots map extra =
    (* Build the dependencies using the regular params and args of
       continuations, and the let-bindings in continuations handlers. *)
    let t =
      Continuation.Map.fold
        (add_continuation_info map ~return_continuation ~exn_continuation
           ~used_value_slots)
        map (empty code_age_relation)
    in
    (* Take into account the extra params and args. *)
    let t =
      Continuation.Map.fold
        (fun _ (extra_params_and_args : Continuation_extra_params_and_args.t) t ->
          Apply_cont_rewrite_id.Map.fold
            (fun _ extra_args t ->
              List.fold_left2
                (fun t extra_param extra_arg ->
                  let src = Name.var (Bound_parameter.var extra_param) in
                  match
                    (extra_arg : Continuation_extra_params_and_args.Extra_arg.t)
                  with
                  | Already_in_scope simple ->
                    Name_occurrences.fold_names (Simple.free_names simple)
                      ~init:t ~f:(fun t dst -> add_dependency ~src ~dst t)
                  | New_let_binding (src', prim) ->
                    let src' = Name.var src' in
                    Name_occurrences.fold_names
                      (Flambda_primitive.free_names prim)
                      ~f:(fun t dst -> add_dependency ~src:src' ~dst t)
                      ~init:(add_dependency ~src ~dst:src' t)
                  | New_let_binding_with_named_args (_src', _prim_gen) ->
                    (* In this case, the free_vars present in the result of
                       _prim_gen are fresh (and a subset of the simples given to
                       _prim_gen) and generated when going up while creating a
                       wrapper continuation for the return of a function
                       application.

                       In that case, the fresh parameters created for the
                       wrapper cannot introduce dependencies to other variables
                       or parameters of continuations.

                       Therefore, in this case, the data_flow analysis is
                       incomplete, and we instead rely on the free_names
                       analysis to eliminate the extra_let binding if it is
                       unneeded. *)
                    t)
                t
                (Bound_parameters.to_list extra_params_and_args.extra_params)
                extra_args)
            extra_params_and_args.extra_args t)
        extra t
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

(* Analysis *)
(* ******** *)

let already_printed = ref false

let analyze ~return_continuation ~exn_continuation ~code_age_relation
    ~used_value_slots ~for_inlining
    ({ stack; map; extra; kinds; dummy_toplevel_cont = _ } as t) =
  Profile.record_call ~accumulate:true "data_flow" (fun () ->
      assert (stack = []);
      let deps =
        Dependency_graph.create map extra ~return_continuation ~exn_continuation
          ~code_age_relation ~used_value_slots
      in
      (* Format.eprintf "/// graph@\n%a@\n@." Dependency_graph._print deps; *)
      let result = Dependency_graph.required_names deps in
      (* Format.eprintf "/// result@\n%a@\n@." _print_result result; *)
      if not for_inlining
      then (
        let _aliases =
          Alias_graph.create map extra ~return_continuation ~exn_continuation
        in
        (* Format.eprintf "/// graph@\n%a@\n@." Alias_graph._print _aliases; *)
        let _graph = Alias_graph.Dom.make_graph _aliases in
        (* Format.eprintf "/// dom_graph@\n%a@\n@." Alias_graph.Dom._print
           _graph; *)
        let _dom = Alias_graph.Dom.dom _graph in
        let _fdom = Alias_graph.Dom.first_dom _dom in

        (* Format.eprintf "/// dom@\n%a@\n@." Alias_graph.Dom._print_result
           _dom; *)
        Format.eprintf "/// substitutions@\n%a@\n@."
          (Variable.Map.print Variable.print)
          _fdom;
        let _cg =
          Control_flow.create t ~return_continuation ~exn_continuation
        in
        if not !already_printed
        then begin
          Format.printf "%a@." Control_flow.print_dot _cg;
          already_printed := true
        end;

        let _req = Control_flow.make_req t _fdom in
        let _req_trans = Control_flow.required_vars t _cg _req in
        let _req_without_scoped = Control_flow.remove_scoped t _cg _req_trans in
        let _req_with_new_cont, _new_conts =
          Control_flow.insert_new_entry_points t _cg _req_without_scoped
        in

        Format.eprintf
          "REQQQ: %a@.RUQQQ: %a@.WITHOUT SCOPED: %a@.WITH NEW CONT: %a@."
          (Continuation.Map.print Variable.Set.print)
          _req
          (Continuation.Map.print Variable.Set.print)
          _req_trans
          (Continuation.Map.print Variable.Set.print)
          _req_without_scoped
          (Continuation.Map.print Variable.Set.print)
          _req_with_new_cont;

        (* let _prov =
         *   Continuation.Map.map (fun elt -> Control_flow.provided elt) t.map
         * in
         * Format.eprintf "PROVIDED: %a@."
         *   (Continuation.Map.print Variable.Set.print)
         *   _prov; *)
        let required_new_args =
          Continuation.Map.map
            (fun req ->
              Bound_parameters.create
              @@ List.map
                   (fun v ->
                     let kind_with_subkind = Variable.Map.find v kinds in
                     Bound_parameter.create v kind_with_subkind)
                   (Variable.Set.elements req))
            (* TODO: use _req_with_new_cont *)
            _req_without_scoped
        in

        Format.eprintf "INFO:@\n%a@\n@." print t;

        ignore required_new_args;
        (* result *)
        { result with aliases = _fdom; required_new_args })
      else result)
