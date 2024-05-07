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

    let ensure_domain acc s =
      Node.Set.fold
        (fun x acc ->
          if Node.Map.mem x acc then acc else Node.Map.add x Node.Set.empty acc)
        s acc

    let from_graph (graph : G.graph) (state : G.state) : SCC.directed_graph =
      G.fold_nodes graph
        (fun n acc ->
          let deps = depset graph n in
          let acc = ensure_domain acc deps in
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
        then begin
          Queue.push n q;
          q_s := Node.Set.remove n !q_s
        end
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
                then begin
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
                    | Some elt_deps -> Node.Set.iter push elt_deps)
                end
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
    if Sys.getenv_opt "SHOWCOMP" <> None
    then begin
      Format.eprintf "ncomps: %d, max size: %d@." (Array.length components)
        (Array.fold_left
           (fun m -> function
             | SCC.No_loop _ -> m
             | SCC.Has_loop l -> max m (List.length l))
           0 components);
      Array.iter
        (function
          | SCC.No_loop id -> Format.eprintf "%a@ " Node.print id
          | SCC.Has_loop l ->
            Format.eprintf "[%a]@ " (Format.pp_print_list Node.print) l)
        components;
      Format.eprintf "@."
    end;
    Array.iter
      (fun component -> fixpoint_component graph state component)
      components

  let check_fixpoint (graph : G.graph) (roots : Node.Set.t) (state : G.state) =
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

(** Represents the part of a value that can be accessed *)
type elt =
  | Top  (** Value completely accessed *)
  | Fields of Code_id_or_name.Set.t Field.Map.t
  | Bottom  (** Value not accessed *)

let pp_elt ppf elt =
  match elt with
  | Top -> Format.pp_print_string ppf "⊤"
  | Bottom -> Format.pp_print_string ppf "⊥"
  | Fields fields ->
    Format.fprintf ppf "{ %a }"
      (Field.Map.print Code_id_or_name.Set.print)
      fields

let less_equal_elt e1 e2 =
  match e1, e2 with
  | Bottom, _ | _, Top -> true
  | (Top | Fields _), Bottom | Top, Fields _ -> false
  | Fields f1, Fields f2 ->
    if f1 == f2
    then true
    else
      let ok = ref true in
      ignore
        (Field.Map.merge
           (fun _ e1 e2 ->
             let e1 = Option.value e1 ~default:Code_id_or_name.Set.empty in
             let e2 = Option.value e2 ~default:Code_id_or_name.Set.empty in
             if not (Code_id_or_name.Set.subset e1 e2) then ok := false;
             None)
           f1 f2);
      !ok

let elt_deps elt =
  match elt with
  | Bottom | Top -> Code_id_or_name.Set.empty
  | Fields f ->
    Field.Map.fold
      (fun _ v acc -> Code_id_or_name.Set.union v acc)
      f Code_id_or_name.Set.empty

let join_elt e1 e2 =
  if e1 == e2
  then e1
  else
    match e1, e2 with
    | Bottom, e | e, Bottom -> e
    | Top, _ | _, Top -> Top
    | Fields f1, Fields f2 ->
      Fields
        (Field.Map.union
           (fun _ e1 e2 -> Some (Code_id_or_name.Set.union e1 e2))
           f1 f2)

let target (dep : dep) : Code_id_or_name.t =
  match dep with
  | Alias n -> Code_id_or_name.name n
  | Contains n -> n
  | Use n -> n
  | Field (_, n) -> Code_id_or_name.name n
  | Block (_, n) -> n
  | Alias_if_def (n, _) -> Code_id_or_name.name n
  | Propagate (n, _) -> Code_id_or_name.name n

let propagate uses (k : Code_id_or_name.t) (elt : elt) (dep : dep) : elt =
  match elt with
  | Bottom -> Bottom
  | Top | Fields _ -> begin
    match dep with
    | Alias _ -> elt
    | Contains _ -> assert false
    | Use _ -> Top
    | Field (f, _) ->
      Fields (Field.Map.singleton f (Code_id_or_name.Set.singleton k))
    | Block (f, _) -> begin
      match elt with
      | Bottom -> assert false
      | Top -> Top
      | Fields fields ->
        let elems =
          match Field.Map.find_opt f fields with
          | None -> Code_id_or_name.Set.empty
          | Some s -> s
        in
        Code_id_or_name.Set.fold
          (fun n acc ->
            join_elt acc
              (match Hashtbl.find_opt uses n with
              | None -> Bottom
              | Some e -> e))
          elems Bottom
    end
    | Alias_if_def (_, c) -> begin
      match Hashtbl.find_opt uses (Code_id_or_name.code_id c) with
      | None | Some Bottom -> Bottom
      | Some (Fields _ | Top) -> elt
    end
    | Propagate (_, n) -> begin
      match Hashtbl.find_opt uses (Code_id_or_name.name n) with
      | None -> Bottom
      | Some elt -> elt
    end
  end

let propagate_top uses (dep : dep) : bool =
  match dep with
  | Alias _ -> true
  | Contains _ -> true
  | Use _ -> true
  | Field _ -> false
  | Block (_, _) -> true
  | Alias_if_def (_, c) -> begin
    match Hashtbl.find_opt uses (Code_id_or_name.code_id c) with
    | None | Some Bottom -> false
    | Some (Fields _ | Top) -> true
  end
  | Propagate (_, n2) -> begin
    match Hashtbl.find_opt uses (Code_id_or_name.name n2) with
    | None | Some (Bottom | Fields _) -> false
    | Some Top -> true
  end

type result = (Code_id_or_name.t, elt) Hashtbl.t

let pp_result ppf (res : result) =
  let elts = List.of_seq @@ Hashtbl.to_seq res in
  let pp ppf l =
    let pp_sep ppf () = Format.fprintf ppf ",@ " in
    let pp ppf (name, elt) =
      Format.fprintf ppf "%a: %a" Code_id_or_name.print name pp_elt elt
    in
    Format.pp_print_list ~pp_sep pp ppf l
  in
  Format.fprintf ppf "@[<hov 2>{@ %a@ }@]" pp elts

module Graph = struct
  type graph = Global_flow_graph.fun_graph

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

  let target = target

  type nonrec elt = elt

  type state = result

  let top = Top

  let is_top = function Top -> true | Bottom | Fields _ -> false

  let is_bottom = function Bottom -> true | Top | Fields _ -> false

  let elt_deps = elt_deps

  let widen _ ~old:elt1 elt2 = join_elt elt1 elt2

  let join _ elt1 elt2 = join_elt elt1 elt2
  (* XXX no need to cut *)

  let less_equal _ elt1 elt2 = less_equal_elt elt1 elt2

  let propagate = propagate

  let propagate_top = propagate_top

  let get state n =
    match Hashtbl.find_opt state n with None -> Bottom | Some elt -> elt

  let set state n elt = Hashtbl.replace state n elt
end

module Solver = Make_Fixpoint (Graph)

let fixpoint (graph_new : Global_flow_graph.fun_graph) =
  let result_topo = Hashtbl.create 17 in
  let uses =
    graph_new.Global_flow_graph.used |> Hashtbl.to_seq_keys |> List.of_seq
    |> Code_id_or_name.Set.of_list
  in
  Solver.fixpoint_topo graph_new uses result_topo;
  Solver.check_fixpoint graph_new uses result_topo;
  (* Hashtbl.iter (fun k _ ->
      if not (Hashtbl.mem result_topo k) then
        Format.eprintf "NOT BOTTOM: %a@." Code_id_or_name.print k;
    ) _result; *)
  (* Format.eprintf "RESULT: %a@." pp_result result_topo; *)
  (* if Sys.getenv_opt "TOTO" <> None then ( Format.eprintf "TOPO:@.%a@.@."
     pp_result result_topo; Format.eprintf "NORMAL:@.%a@.@." pp_result result);
     if not (Dep_solver_safe.equal_result result_topo result) then begin
     Format.printf "NOT EQUAL:@.%a@.XXX@.%a@.END@.XXXXXXX@.DIFF:@." pp_result
     result_topo pp_result result; Dep_solver_safe.print_diff result
     result_topo; assert false end; assert (Dep_solver_safe.equal_result
     result_topo result); *)
  result_topo
