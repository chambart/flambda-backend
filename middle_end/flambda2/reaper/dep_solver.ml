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

type dep = Global_flow_graph.Dep.t

module Field = Global_flow_graph.Field

module type Graph = sig
  type graph

  module Node : Container_types.S

  type edge

  val fold_nodes : graph -> (Node.t -> 'a -> 'a) -> 'a -> 'a

  val fold_edges : graph -> Node.t -> (edge -> 'a -> 'a) -> 'a -> 'a

  val target : edge -> Node.t

  type state

  type elt

  val top : elt

  val is_top : elt -> bool

  val is_bottom : elt -> bool

  val elt_deps : elt -> Node.Set.t

  val join : state -> elt -> elt -> elt

  val widen : state -> old:elt -> elt -> elt

  val less_equal : state -> elt -> elt -> bool

  val propagate : state -> Node.t -> elt -> edge -> elt

  val propagate_top : state -> edge -> bool

  val get : state -> Node.t -> elt

  val set : state -> Node.t -> elt -> unit
end

module Make_Fixpoint (G : Graph) = struct
  module Node = G.Node
  module SCC = Strongly_connected_components.Make (Node)

  module Make_SCC = struct
    let depset (graph : G.graph) (n : Node.t) : Node.Set.t =
      G.fold_edges graph n
        (fun edge acc -> Node.Set.add (G.target edge) acc)
        Node.Set.empty

    let complete_domain acc s =
      Node.Set.fold
        (fun x acc ->
          if Node.Map.mem x acc then acc else Node.Map.add x Node.Set.empty acc)
        s acc

    let from_graph (graph : G.graph) (state : G.state) : SCC.directed_graph =
      G.fold_nodes graph
        (fun n acc ->
          let deps = depset graph n in
          let acc = complete_domain acc deps in
          (* For nodes which are already as [top], the fixpoint is already
             reached. We can safely ignore the dependency and process these
             nodes at the beginning, cutting some cycles. *)
          let deps =
            Node.Set.filter
              (fun other -> not (G.is_top (G.get state other)))
              deps
          in
          Node.Map.add n deps acc)
        Node.Map.empty
  end

  let propagate_tops (graph : G.graph) (roots : Node.Set.t) (state : G.state) =
    let rec loop stack =
      match stack with
      | [] -> ()
      | n :: stack ->
        let stack =
          G.fold_edges graph n
            (fun dep stack ->
              if G.propagate_top state dep
              then
                let target = G.target dep in
                if G.is_top (G.get state target)
                then stack
                else (
                  G.set state n G.top;
                  target :: stack)
              else stack)
            stack
        in
        loop stack
    in
    let stack = Node.Set.elements roots in
    List.iter (fun n -> G.set state n G.top) stack;
    loop stack

  let fixpoint_component (graph : G.graph) (state : G.state)
      (component : SCC.component) =
    match component with
    | No_loop id ->
      let current_elt = G.get state id in
      if not (G.is_bottom current_elt)
      then
        G.fold_edges graph id
          (fun dep () ->
            let propagated = G.propagate state id current_elt dep in
            if not (G.is_bottom propagated)
            then
              let target = G.target dep in
              let old = G.get state target in
              G.set state target (G.join state old propagated))
          ()
    | Has_loop ids ->
      let q = Queue.create () in
      (* Invariants: [!q_s] contails the elements that may be pushed in [q],
         that is, the elements of [ids] that are not already in [q]. *)
      let in_loop = Node.Set.of_list ids in
      let q_s = ref Node.Set.empty in
      let to_recompute_deps = Hashtbl.create 17 in
      List.iter (fun id -> Queue.push id q) ids;
      let push n =
        if Node.Set.mem n !q_s
        then (
          Queue.push n q;
          q_s := Node.Set.remove n !q_s)
      in
      let propagate id =
        let current_elt = G.get state id in
        if not (G.is_bottom current_elt)
        then
          G.fold_edges graph id
            (fun dep () ->
              let propagated = G.propagate state id current_elt dep in
              if not (G.is_bottom propagated)
              then
                let target = G.target dep in
                let old = G.get state target in
                if Node.Set.mem target in_loop
                then (
                  let widened = G.widen state ~old propagated in
                  if not (G.less_equal state widened old)
                  then (
                    let new_deps = G.elt_deps widened in
                    Node.Set.iter
                      (fun elt_dep ->
                        Hashtbl.replace to_recompute_deps elt_dep
                          (Node.Set.add target
                             (Option.value ~default:Node.Set.empty
                                (Hashtbl.find_opt to_recompute_deps elt_dep))))
                      new_deps;
                    G.set state target widened;
                    push target;
                    match Hashtbl.find_opt to_recompute_deps target with
                    | None -> ()
                    | Some elt_deps -> Node.Set.iter push elt_deps))
                else G.set state target (G.join state old propagated))
            ()
      in
      while not (Queue.is_empty q) do
        let n = Queue.pop q in
        q_s := Node.Set.add n !q_s;
        propagate n
      done

  let fixpoint_topo (graph : G.graph) (roots : Node.Set.t) (state : G.state) =
    propagate_tops graph roots state;
    let components =
      SCC.connected_components_sorted_from_roots_to_leaf
        (Make_SCC.from_graph graph state)
    in
    Array.iter
      (fun component -> fixpoint_component graph state component)
      components

  let check_fixpoint (graph : G.graph) (roots : Node.Set.t) (state : G.state) =
    (* Checks that the given state is a post-fixpoint for propagation, and that
       all roots are set to [Top]. *)
    Node.Set.iter
      (fun root -> assert (G.less_equal state G.top (G.get state root)))
      roots;
    G.fold_nodes graph
      (fun node () ->
        G.fold_edges graph node
          (fun dep () ->
            assert (
              G.less_equal state
                (G.propagate state node (G.get state node) dep)
                (G.get state (G.target dep))))
          ())
      ()
end

type field_elt =
  | Field_top
  | Field_vals of Code_id_or_name.Set.t

(** Represents the part of a value that can be accessed *)
type elt =
  | Top  (** Value completely accessed *)
  | Fields of
      { fields : field_elt Field.Map.t;
        uses : Code_id_or_name.Set.t
      }
      (** Only the given fields are accessed, each field either being completely accessed for [Field_top]
      or corresponding to the union of all the elements corresponding to all the
      [Code_id_or_name.t] in the set for [Field_vals]. *)
  | Bottom  (** Value not accessed *)

let pp_field_elt ppf elt =
  match elt with
  | Field_top -> Format.pp_print_string ppf "⊤"
  | Field_vals s -> Code_id_or_name.Set.print ppf s

let pp_elt ppf elt =
  match elt with
  | Top -> Format.pp_print_string ppf "⊤"
  | Bottom -> Format.pp_print_string ppf "⊥"
  | Fields fields ->
    Format.fprintf ppf "{ fields: %a; uses : %a }"
      (Field.Map.print pp_field_elt)
      fields.fields Code_id_or_name.Set.print fields.uses

module Graph = struct
  type graph = Global_flow_graph.graph

  module Node = Code_id_or_name

  type edge = Global_flow_graph.Dep.t

  let fold_nodes graph f init =
    Hashtbl.fold
      (fun n _ acc -> f n acc)
      graph.Global_flow_graph.name_to_dep init

  let fold_edges graph n f init =
    match Hashtbl.find_opt graph.Global_flow_graph.name_to_dep n with
    | None -> init
    | Some deps -> Global_flow_graph.Dep.Set.fold f deps init

  let target (dep : dep) : Code_id_or_name.t =
    match dep with
    | Alias { target }
    | Accessor { target; _ }
    | Alias_if_def { target; _ }
    | Propagate { target; _ } ->
      Code_id_or_name.name target
    | Use { target } | Constructor { target; _ } -> target

  type nonrec elt = elt

  let less_equal_elt e1 e2 =
    match e1, e2 with
    | Bottom, _ | _, Top -> true
    | (Top | Fields _), Bottom | Top, Fields _ -> false
    | Fields f1, Fields f2 ->
      if f1.uses == f2.uses && f1.fields == f2.fields
      then true
      else
        Code_id_or_name.Set.subset f1.uses f2.uses
        &&
        let ok = ref true in
        ignore
          (Field.Map.merge
             (fun _ e1 e2 ->
               (match e1, e2 with
               | None, _ -> ()
               | Some _, None -> ok := false
               | _, Some Field_top -> ()
               | Some Field_top, _ -> ok := false
               | Some (Field_vals e1), Some (Field_vals e2) ->
                 if not (Code_id_or_name.Set.subset e1 e2) then ok := false);
               None)
             f1.fields f2.fields);
        !ok

  let elt_deps elt =
    match elt with
    | Bottom | Top -> Code_id_or_name.Set.empty
    | Fields f ->
      Field.Map.fold
        (fun _ v acc ->
          match v with
          | Field_top -> acc
          | Field_vals v -> Code_id_or_name.Set.union v acc)
        f.fields Code_id_or_name.Set.empty

  let join_elt e1 e2 =
    if e1 == e2
    then e1
    else
      match e1, e2 with
      | Bottom, e | e, Bottom -> e
      | Top, _ | _, Top -> Top
      | Fields f1, Fields f2 ->
        let fields =
          Field.Map.union
            (fun _ e1 e2 ->
              match e1, e2 with
              | Field_top, _ | _, Field_top -> Some Field_top
              | Field_vals e1, Field_vals e2 ->
                Some (Field_vals (Code_id_or_name.Set.union e1 e2)))
            f1.fields f2.fields
        in
        let uses = Code_id_or_name.Set.union f1.uses f2.uses in
        Fields { fields; uses }

  let make_field_elt uses (k : Code_id_or_name.t) =
    match Hashtbl.find_opt uses k with
    | Some Top -> Field_top
    | None | Some (Bottom | Fields _) ->
      Field_vals (Code_id_or_name.Set.singleton k)

  let propagate uses (k : Code_id_or_name.t) (elt : elt) (dep : dep) : elt =
    match elt with
    | Bottom -> Bottom
    | Top | Fields _ -> (
      match dep with
      | Alias _ -> elt
      | Use _ -> Top
      | Accessor { relation; target } ->
        let fields = Field.Map.singleton relation (make_field_elt uses k) in
        let uses =
          Code_id_or_name.Set.singleton (Code_id_or_name.name target)
        in
        Fields { fields; uses }
      | Constructor { relation; _ } -> (
        match elt with
        | Bottom -> assert false
        | Top -> Top
        | Fields fields -> (
          try
            let elems =
              match Field.Map.find_opt relation fields.fields with
              | None -> Code_id_or_name.Set.empty
              | Some Field_top -> raise Exit
              | Some (Field_vals s) -> s
            in
            Code_id_or_name.Set.fold
              (fun n acc ->
                join_elt acc
                  (match Hashtbl.find_opt uses n with
                  | None -> Bottom
                  | Some e -> e))
              elems Bottom
          with Exit -> Top))
      | Alias_if_def { if_defined; _ } -> (
        match Hashtbl.find_opt uses if_defined with
        | None | Some Bottom -> Bottom
        | Some (Fields _ | Top) -> elt)
      | Propagate { source; _ } -> (
        match Hashtbl.find_opt uses source with
        | None -> Bottom
        | Some elt -> elt))

  let propagate_top uses (dep : dep) : bool =
    match dep with
    | Alias _ -> true
    | Use _ -> true
    | Accessor _ -> false
    | Constructor _ -> true
    | Alias_if_def { if_defined; _ } -> (
      match Hashtbl.find_opt uses if_defined with
      | None | Some Bottom -> false
      | Some (Fields _ | Top) -> true)
    | Propagate { source; _ } -> (
      match Hashtbl.find_opt uses source with
      | None | Some (Bottom | Fields _) -> false
      | Some Top -> true)

  let top = Top

  let is_top = function Top -> true | Bottom | Fields _ -> false

  let is_bottom = function Bottom -> true | Top | Fields _ -> false

  let widen _ ~old:elt1 elt2 = join_elt elt1 elt2

  let join _ elt1 elt2 = join_elt elt1 elt2

  let less_equal _ elt1 elt2 = less_equal_elt elt1 elt2

  type state = (Code_id_or_name.t, elt) Hashtbl.t

  let get state n =
    match Hashtbl.find_opt state n with None -> Bottom | Some elt -> elt

  let set state n elt = Hashtbl.replace state n elt
end

module Solver = Make_Fixpoint (Graph)

module Dual_graph = struct
  include Global_flow_graph.Dual
  module Node = Code_id_or_name

  type field_elt =
    | Field_top
    | Field_vals of Code_id_or_name.Set.t

  type elt =
    | Top  (** Any value can flow to this variable *)
    | Block of
        { fields : field_elt Field.Map.t;
          sources : Code_id_or_name.Set.t
        }
        (** This value can be produced at any of those sources.
          Its value can be extracted from the fields of those field sources  *)
    | Bottom  (** No value can flow here *)

  let pp_field_elt ppf elt =
    match elt with
    | Field_top -> Format.pp_print_string ppf "⊤"
    | Field_vals s -> Code_id_or_name.Set.print ppf s

  let pp_elt ppf elt =
    match elt with
    | Top -> Format.pp_print_string ppf "⊤"
    | Bottom -> Format.pp_print_string ppf "⊥"
    | Block { fields; sources } ->
      Format.fprintf ppf "@[<hov 2>{@ sources: %a;@ fields: %a }@]"
        Code_id_or_name.Set.print sources
        (Field.Map.print pp_field_elt)
        fields

  let fold_nodes (graph : graph) f init =
    Code_id_or_name.Map.fold (fun n _ acc -> f n acc) graph init

  let fold_edges (type a) (graph : graph) (n : Node.t) (f : edge -> a -> a)
      (init : a) : a =
    match Code_id_or_name.Map.find_opt n graph with
    | None -> init
    | Some deps -> List.fold_left (Fun.flip f) init deps

  let target (dep : edge) : Code_id_or_name.t =
    match dep with
    | Alias { target } | Accessor { target; _ } | Constructor { target; _ } ->
      target

  let less_equal_elt (e1 : elt) (e2 : elt) =
    match e1, e2 with
    | Bottom, _ | _, Top -> true
    | (Top | Block _), Bottom | Top, Block _ -> false
    | Block f1, Block f2 ->
      if e1 == e2
      then true
      else
        Code_id_or_name.Set.subset f1.sources f2.sources
        &&
        let ok = ref true in
        ignore
          (Field.Map.merge
             (fun _ e1 e2 ->
               (match e1, e2 with
               | None, _ -> ()
               | Some _, None -> ok := false
               | _, Some Field_top -> ()
               | Some Field_top, _ -> ok := false
               | Some (Field_vals e1), Some (Field_vals e2) ->
                 if not (Code_id_or_name.Set.subset e1 e2) then ok := false);
               None)
             f1.fields f2.fields);
        !ok

  let elt_deps elt =
    match elt with
    | Bottom | Top -> Code_id_or_name.Set.empty
    | Block f ->
      Field.Map.fold
        (fun _ v acc ->
          match v with
          | Field_top -> acc
          | Field_vals v -> Code_id_or_name.Set.union v acc)
        f.fields Code_id_or_name.Set.empty

  let join_elt e1 e2 =
    if e1 == e2
    then e1
    else
      match e1, e2 with
      | Bottom, e | e, Bottom -> e
      | Top, _ | _, Top -> Top
      | Block f1, Block f2 ->
        let fields =
          Field.Map.union
            (fun _ e1 e2 ->
              match e1, e2 with
              | Field_top, _ | _, Field_top -> Some Field_top
              | Field_vals e1, Field_vals e2 ->
                Some (Field_vals (Code_id_or_name.Set.union e1 e2)))
            f1.fields f2.fields
        in
        let sources = Code_id_or_name.Set.union f1.sources f2.sources in
        Block { fields; sources }

  let make_field_elt sources (k : Code_id_or_name.t) =
    match Hashtbl.find_opt sources k with
    | Some Top -> Field_top
    | None | Some (Bottom | Block _) ->
      Field_vals (Code_id_or_name.Set.singleton k)

  let propagate sources (k : Code_id_or_name.t) (elt : elt) (dep : edge) : elt =
    match elt with
    | Bottom -> Bottom
    | Top | Block _ -> (
      match dep with
      | Alias _ -> elt
      | Constructor { relation; target } ->
        Block
          { fields = Field.Map.singleton relation (make_field_elt sources k);
            sources = Code_id_or_name.Set.singleton target
          }
      | Accessor { relation; _ } -> (
        match elt with
        | Bottom -> assert false
        | Top -> Top
        | Block { fields; _ } -> (
          try
            let elems =
              match Field.Map.find_opt relation fields with
              | None -> Code_id_or_name.Set.empty
              | Some Field_top -> raise Exit
              | Some (Field_vals s) -> s
            in
            Code_id_or_name.Set.fold
              (fun n acc ->
                join_elt acc
                  (match Hashtbl.find_opt sources n with
                  | None -> Bottom
                  | Some e -> e))
              elems Bottom
          with Exit -> Top)))

  let propagate_top _sources (dep : edge) : bool =
    match dep with
    | Alias _ -> true
    | Constructor _ -> false
    | Accessor _ -> true

  let top = Top

  let is_top = function Top -> true | Bottom | Block _ -> false

  let is_bottom = function Bottom -> true | Top | Block _ -> false

  let widen _ ~old:elt1 elt2 = join_elt elt1 elt2

  let join _ elt1 elt2 = join_elt elt1 elt2

  let less_equal _ elt1 elt2 = less_equal_elt elt1 elt2

  type state = (Code_id_or_name.t, elt) Hashtbl.t

  let get state n =
    match Hashtbl.find_opt state n with None -> Bottom | Some elt -> elt

  let set state n elt = Hashtbl.replace state n elt

  let build_dual (graph : Graph.graph) (solution : Graph.state) :
      graph * Code_id_or_name.Set.t =
    let add graph from to_ =
      Code_id_or_name.Map.update from
        (function None -> Some [to_] | Some l -> Some (to_ :: l))
        graph
    in
    (* top_roots is the initialization of the fixpoint. We can only consider top
       values as potential roots because we think that every constructor descend
       from one that has at least one top as its arguments. This is somewhat
       safe because atomic values are top (let x = 1: x would be top) and there
       are no purely cyclic values, for instance let rec x = x :: x would be
       initialized from external C functions (so Top). And a loop produced
       through a function cannot terminate (let rec loop () = (loop ()) :: (loop
       ())), hence the value is never produced. Note that this last case might
       actually be tricky (dead code still has to be compiled) *)
    let top_roots = ref Code_id_or_name.Set.empty in
    let graph =
      Hashtbl.fold
        (fun node (deps : Global_flow_graph.Dep.Set.t) acc ->
          Global_flow_graph.Dep.Set.fold
            (fun dep acc ->
              match dep with
              | Alias { target } ->
                add acc (Code_id_or_name.name target) (Alias { target = node })
              | Alias_if_def { if_defined; target } -> (
                match Hashtbl.find_opt solution if_defined with
                | None | Some Bottom -> acc
                | Some (Fields _ | Top) ->
                  add acc
                    (Code_id_or_name.name target)
                    (Alias { target = node }))
              | Propagate _ ->
                (* CR ncourant/pchambart: verify the invariant that this edge
                   should already be in the graph (or added later) by an
                   alias_if_def *)
                acc
              | Constructor { relation; target } ->
                add acc target (Constructor { relation; target = node })
              | Accessor { relation; target } ->
                add acc
                  (Code_id_or_name.name target)
                  (Accessor { relation; target = node })
              | Use _ ->
                top_roots := Code_id_or_name.Set.add node !top_roots;
                acc)
            deps acc)
        graph.name_to_dep Code_id_or_name.Map.empty
    in
    graph, !top_roots
end

module Alias_solver = Make_Fixpoint (Dual_graph)

type use_result = Graph.state

type alias_result = Dual_graph.state

type 'a unboxed_fields =
  | Not_unboxed of 'a
  | Unboxed of 'a unboxed_fields Field.Map.t

let rec pp_unboxed_elt pp_unboxed ppf = function
  | Not_unboxed x -> pp_unboxed ppf x
  | Unboxed fields -> Field.Map.print (pp_unboxed_elt pp_unboxed) ppf fields

(*
type repr =
  | Unboxed_fields of Variable.t unboxed_fields
  | Changed_representation of Field.t unboxed_fields
*)

type assigned = Variable.t unboxed_fields Code_id_or_name.Map.t

type result =
  { uses : use_result;
    aliases : alias_result;
    dual_graph : Dual_graph.graph;
    unboxed_fields : assigned;
    (* CR: [(Field.t, Constant.t) Either.t unboxed_fields Code_id_or_name.Map.t] ? *)
    changed_representation : Field.t unboxed_fields Code_id_or_name.Map.t;
  }

let pp_result ppf (res : use_result) =
  let elts = List.of_seq @@ Hashtbl.to_seq res in
  let pp ppf l =
    let pp_sep ppf () = Format.fprintf ppf ",@ " in
    let pp ppf (name, elt) =
      Format.fprintf ppf "%a: %a" Code_id_or_name.print name pp_elt elt
    in
    Format.pp_print_list ~pp_sep pp ppf l
  in
  Format.fprintf ppf "@[<hov 2>{@ %a@ }@]" pp elts

let pp_dual_result ppf (res : Dual_graph.state) =
  let elts = List.of_seq @@ Hashtbl.to_seq res in
  let pp ppf l =
    let pp_sep ppf () = Format.fprintf ppf ",@ " in
    let pp ppf (name, elt) =
      Format.fprintf ppf "%a: %a" Code_id_or_name.print name Dual_graph.pp_elt
        elt
    in
    Format.pp_print_list ~pp_sep pp ppf l
  in
  Format.fprintf ppf "@[<hov 2>{@ %a@ }@]" pp elts

type problematic_uses =
  | Cannot_unbox_due_to_uses
  | No_problem of { use_aliases : Code_id_or_name.Set.t }

let problematic_uses ~for_destructuring_value elt =
  match elt with
  | Top -> Cannot_unbox_due_to_uses
  | Bottom ->
    No_problem { use_aliases = Code_id_or_name.Set.empty }
    (* Cannot_unbox_due_to_uses *)
  | Fields { fields; uses } ->
    if for_destructuring_value
       && Field.Map.exists
            (fun (field : Field.t) _ ->
              match[@ocaml.warning "-4"] field with
              (* We probably cannot destructure a closure that is called
                 somewhere. *)
              | Code_of_closure | Apply _ -> true
              | _ -> false)
            fields
    then Cannot_unbox_due_to_uses
    else No_problem { use_aliases = uses }

let can_change_representation ~for_destructuring_value dual graph allocation_id
    =
  (* The representation can be changed only if we can track its uses. And all
     the use sites can be changed. If a different value where to flow to that
     same use site, it would not be possible to change the representation.

     Note: This alias constraint is not a strict requirement, we might lighten
     that later. *)
  let uses =
    match Hashtbl.find_opt graph allocation_id with
    | None -> Bottom
    | Some uses -> uses
  in
  match problematic_uses ~for_destructuring_value uses with
  | Cannot_unbox_due_to_uses -> false
  | No_problem { use_aliases } ->
    let alias_dominated_by_allocation_id alias =
      match (Hashtbl.find_opt dual alias : Dual_graph.elt option) with
      | None -> true
      | Some Bottom -> true 
      | Some Top -> false
      | Some (Block { sources; _ }) ->
        Code_id_or_name.Set.equal
          (Code_id_or_name.Set.singleton allocation_id)
          sources
    in
    alias_dominated_by_allocation_id allocation_id
    && Code_id_or_name.Set.for_all alias_dominated_by_allocation_id use_aliases

let map_from_allocation_points_to_dominated dual =
  let map = ref Code_id_or_name.Map.empty in
  Hashtbl.iter
    (fun id (elt : Dual_graph.elt) ->
      match elt with
      | Bottom | Top -> ()
      | Block { sources; _ } -> (
        (* Sources are only allocation points, so if sources is not a singleton,
           then id has no dominator that can be an allocation point. *)
        match Code_id_or_name.Set.get_singleton sources with
        | None -> ()
        | Some elt ->
          map
            := Code_id_or_name.Map.update elt
                 (function
                   | None -> Some (Code_id_or_name.Set.singleton id)
                   | Some set -> Some (Code_id_or_name.Set.add id set))
                 !map))
    dual;
  !map
(*
let rec mapi_unboxed_fields (not_unboxed : 'a -> 'b -> 'c) (unboxed : Field.t -> 'a -> 'a) (acc : 'a) (uf : 'b unboxed_fields) : 'c unboxed_fields =
  match uf with
  | Not_unboxed x -> Not_unboxed (not_unboxed acc x)
  | Unboxed f ->
      Unboxed (Field.Map.mapi (fun field uf -> mapi_unboxed_fields not_unboxed unboxed (unboxed field acc) uf) f)

let map_unboxed_fields f uf = mapi_unboxed_fields (fun () x -> f x) (fun _ () -> ()) () uf
*)
let can_unbox dual dual_graph graph ~dominated_by_allocation_points
    allocation_id =
  can_change_representation ~for_destructuring_value:true dual graph
    allocation_id
  &&
  let aliases =
    match Code_id_or_name.Map.find_opt allocation_id dominated_by_allocation_points with Some x -> x | None -> Code_id_or_name.Set.empty
  in
  Code_id_or_name.Set.for_all
    (fun alias ->
      let edges = Code_id_or_name.Map.find alias dual_graph in
      List.for_all
        (fun (edge : Dual_graph.edge) ->
          match edge with
          | Alias _ | Accessor _ -> true
          | Constructor { target; relation } ->
            let target_uses =
              match Hashtbl.find_opt graph target with
              | None -> Bottom
              | Some t -> t
            in
            let relation_is_used =
              match target_uses with
              | Bottom -> false
              | Top -> true
              | Fields { fields; _ } -> Field.Map.mem relation fields
            in
            (not relation_is_used)
            ||
            let relation_prevents_unboxing =
              match relation with
              | Field.Block _ -> false
              | Field.Value_slot _ -> false
              | Field.Function_slot _ -> true
              | Field.Code_of_closure -> true
              | Field.Is_int -> true
              | Field.Get_tag -> true
              | Field.Apply (_, _) ->
                (* This requires unboxing returns of function, maybe later *)
                let unclear = true in
                unclear
            in
            (not relation_prevents_unboxing)
            && can_change_representation ~for_destructuring_value:false dual
                 graph target)
        edges)
    aliases

let fixpoint (graph_new : Global_flow_graph.graph) =
  let result = Hashtbl.create 17 in
  let uses =
    graph_new.Global_flow_graph.used |> Hashtbl.to_seq_keys |> List.of_seq
    |> Code_id_or_name.Set.of_list
  in
  Solver.fixpoint_topo graph_new uses result;
  Solver.check_fixpoint graph_new uses result;
  let dual_graph, roots = Dual_graph.build_dual graph_new result in
  let aliases = Hashtbl.create 17 in
  Alias_solver.fixpoint_topo dual_graph roots aliases;
  Format.eprintf "@.SAUCISSE XXX@.@.@.";
  let dominated_by_allocation_points =
    map_from_allocation_points_to_dominated aliases
  in
  let allocation_point_dominator =
    Code_id_or_name.Map.fold (fun alloc_point dominated acc ->
        Code_id_or_name.Set.fold (fun dom acc -> Code_id_or_name.Map.add dom alloc_point acc)
        dominated acc)
      dominated_by_allocation_points Code_id_or_name.Map.empty
  in
  Hashtbl.iter
    (fun code_or_name elt ->
      if can_change_representation ~for_destructuring_value:true aliases result
           code_or_name
      then
        let path =
          match Code_id_or_name.Map.find_opt code_or_name dominated_by_allocation_points with Some x -> x | None -> Code_id_or_name.Set.empty
        in
        Format.eprintf "%a => %a@.%a@." Code_id_or_name.print code_or_name
          pp_elt elt Code_id_or_name.Set.print path)
    result;
  Format.eprintf "@.UNBOXABLE XXX@.@.@.";
  let assigned : assigned ref = ref Code_id_or_name.Map.empty in
  let to_unbox = Hashtbl.fold (fun code_or_name _elt to_unbox ->
    if can_unbox aliases dual_graph result ~dominated_by_allocation_points code_or_name then
      Code_id_or_name.Set.add code_or_name to_unbox
    else
      to_unbox
    ) result Code_id_or_name.Set.empty
  in
  let to_change_representation = Hashtbl.fold (fun code_or_name _elt to_change_representation ->
    if not (Code_id_or_name.Set.mem code_or_name to_unbox) && can_change_representation ~for_destructuring_value:false aliases result code_or_name then
      Code_id_or_name.Set.add code_or_name to_change_representation
    else
      to_change_representation
    ) result Code_id_or_name.Set.empty
  in
  let has_to_be_unboxed code_or_name =
    match Code_id_or_name.Map.find_opt code_or_name allocation_point_dominator with
    | None -> false
    | Some alloc_point -> Code_id_or_name.Set.mem alloc_point to_unbox
  in
  Code_id_or_name.Set.iter
    (fun code_or_name ->
        Format.eprintf "%a@." Code_id_or_name.print code_or_name;
        let to_patch =
          match Code_id_or_name.Map.find_opt code_or_name dominated_by_allocation_points with None -> Code_id_or_name.Set.empty | Some x -> x
        in
        Code_id_or_name.Set.iter
          (fun to_patch ->
            let rec unbox_elt elt name_prefix =
              match elt with
              | Top ->
                  Misc.fatal_errorf "Trying to unbox Top uses when unboxing %a" Code_id_or_name.print to_patch
              | Bottom -> Unboxed Field.Map.empty
              | Fields { fields; _ } ->
                Unboxed (Field.Map.mapi
                  (fun field field_elt ->
                     let new_name = Flambda_colours.without_colours ~f:(fun () -> Format.asprintf "%s_field_%a" name_prefix Field.print field) in
                    let[@local] default () =
                    (* TODO let ghost for debugging *)
                    Not_unboxed (Variable.create new_name)
                    in
                    match field_elt with
                    | Field_top -> default ()
                    | Field_vals flow_to ->
                      if Code_id_or_name.Set.is_empty flow_to then
                        Misc.fatal_errorf "Empty set in [Field_vals]";
                      if Code_id_or_name.Set.for_all has_to_be_unboxed 
                        flow_to
                      then
                        let elt = Code_id_or_name.Set.fold (fun flow acc ->
                          match Hashtbl.find_opt result flow with
                            | None -> Misc.fatal_errorf "%a is in [Field_vals] but not in result" Code_id_or_name.print flow
                            | Some elt -> Graph.join_elt acc elt
                          ) flow_to Bottom
                        in
                        unbox_elt elt new_name
                      else if Code_id_or_name.Set.exists has_to_be_unboxed flow_to then
                        Misc.fatal_errorf "Field %a of %s flows to both unboxed and non-unboxed variables"
                          Field.print field name_prefix
                      else
                        default ()
                  ) fields)
            in
            let new_name = Flambda_colours.without_colours ~f:(fun () ->
                Format.asprintf "%a_into_%a" Code_id_or_name.print code_or_name Code_id_or_name.print to_patch)
            in
            let fields =
              match Hashtbl.find_opt result to_patch with
              | None -> Unboxed Field.Map.empty
              | Some elt -> unbox_elt elt new_name
            in
            assigned := Code_id_or_name.Map.add to_patch fields !assigned)
          to_patch)
    to_unbox;
  Format.printf "new vars: %a"
    (Code_id_or_name.Map.print (pp_unboxed_elt Variable.print))
    !assigned;
  let changed_representation = ref Code_id_or_name.Map.empty in
  Code_id_or_name.Set.iter (fun code_id_or_name ->
    let uses = match Hashtbl.find_opt result code_id_or_name with None -> Bottom | Some x -> x in
      let r = ref ~-1 in
      let mk_field () =
        incr r; Field.Block (!r, Flambda_kind.value)
      in
    let repr = let rec repr_elt = function
    | Top -> Misc.fatal_errorf "Cannot change representation of Top for %a" Code_id_or_name.print code_id_or_name
    | Bottom -> Unboxed Field.Map.empty
    | Fields {fields; _} ->
      (* TODO handle closures & non-value fields *)
      Unboxed (Field.Map.mapi (fun field field_elt ->
            match field_elt with
            | Field_top -> Not_unboxed (mk_field ())
            | Field_vals flow_to ->
                      if Code_id_or_name.Set.is_empty flow_to then
                        Misc.fatal_errorf "Empty set in [Field_vals]";
                      if Code_id_or_name.Set.for_all has_to_be_unboxed 
                        flow_to
                      then
                        let elt = Code_id_or_name.Set.fold (fun flow acc ->
                          match Hashtbl.find_opt result flow with
                            | None -> Misc.fatal_errorf "%a is in [Field_vals] but not in result" Code_id_or_name.print flow
                            | Some elt -> Graph.join_elt acc elt
                          ) flow_to Bottom
                        in
                        repr_elt elt
                      else if Code_id_or_name.Set.exists has_to_be_unboxed flow_to then
                        Misc.fatal_errorf "Field %a of %a flows to both unboxed and non-unboxed variables"
                          Field.print field Code_id_or_name.print code_id_or_name
                      else
                        Not_unboxed (mk_field ())
                  ) fields)
in repr_elt uses in
    Code_id_or_name.Set.iter (fun c ->
    changed_representation := Code_id_or_name.Map.add c repr !changed_representation)
      (Code_id_or_name.Map.find code_id_or_name dominated_by_allocation_points)
    ) to_change_representation;
  Format.eprintf "@.TO_CHG: %a@." (Code_id_or_name.Map.print (pp_unboxed_elt Field.print)) !changed_representation;
  { uses = result; aliases; dual_graph; unboxed_fields = !assigned; changed_representation = !changed_representation }
