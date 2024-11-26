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

open! Flambda.Import
open! Rev_expr
module Float = Numeric_types.Float_by_bit_pattern
module Float32 = Numeric_types.Float32_by_bit_pattern
module RE = Rebuilt_expr
module Field = Global_flow_graph.Field

type rev_expr = Rev_expr.t

let all_slot_offsets = ref Slot_offsets.empty

let all_code = ref Code_id.Map.empty

type env =
  { uses : Dep_solver.result;
    get_code_metadata : Code_id.t -> Code_metadata.t;
    cont_params_to_keep : bool list Continuation.Map.t;
    should_keep_param : Continuation.t -> Variable.t -> bool;
    function_params_to_keep : bool list Code_id.Map.t;
    should_keep_function_param : Code_id.t -> Variable.t -> bool;
  }

let is_used (env : env) cn = Hashtbl.mem env.uses.uses cn

let is_code_id_used (env : env) code_id =
  is_used env (Code_id_or_name.code_id code_id)
  || not (Compilation_unit.is_current (Code_id.get_compilation_unit code_id))

let is_name_used (env : env) name = is_used env (Code_id_or_name.name name)

let is_var_used (env : env) var = is_used env (Code_id_or_name.var var)

let is_symbol_used (env : env) symbol =
  is_used env (Code_id_or_name.symbol symbol)

let poison_value = 0 (* 123456789 *)

let poison kind = Simple.const_int_of_kind kind poison_value

let rewrite_simple kinds (env : env) simple =
  Simple.pattern_match simple
    ~name:(fun name ~coercion:_ ->
      if is_name_used env name
      then simple
      else
        let kind =
          match Name.Map.find_opt name kinds with
          | Some k -> k
          | None ->
            if Name.is_symbol name
            then Flambda_kind.value
            else Misc.fatal_errorf "Unbound name %a" Name.print name
        in
        poison kind)
    ~const:(fun _ -> simple)

let rewrite_simple_opt (env : env) = function
  | None -> None
  | Some simple as simpl ->
    Simple.pattern_match simple
      ~name:(fun name ~coercion:_ ->
        if is_name_used env name then simpl else None)
      ~const:(fun _ -> simpl)

let rewrite_or_variable default env (or_variable : _ Or_variable.t) =
  match or_variable with
  | Const _ -> or_variable
  | Var (v, _) ->
    if is_var_used env v then or_variable else Or_variable.Const default

let rewrite_simple_with_debuginfo kinds env (simple : Simple.With_debuginfo.t) =
  Simple.With_debuginfo.create
    (rewrite_simple kinds env (Simple.With_debuginfo.simple simple))
    (Simple.With_debuginfo.dbg simple)

let rewrite_static_const kinds (env : env) (sc : Static_const.t) =
  match sc with
  | Set_of_closures sc ->
    let function_decls = Set_of_closures.function_decls sc in
    let function_decls =
      let module FD = Function_declarations in
      FD.create
        (Function_slot.Lmap.mapi
           (fun _slot (code_id : FD.code_id_in_function_declaration) :
                FD.code_id_in_function_declaration ->
             match code_id with
             | Deleted _ -> code_id
             | Code_id code_id ->
               if is_code_id_used env code_id
               then Code_id code_id
               else
                 let code_metadata = env.get_code_metadata code_id in
                 Deleted
                   { function_slot_size =
                       Code_metadata.function_slot_size code_metadata;
                     dbg = Code_metadata.dbg code_metadata
                   })
           (FD.funs_in_order function_decls))
    in
    let set_of_closures =
      Set_of_closures.create
        ~value_slots:
          (Value_slot.Map.map (rewrite_simple kinds env)
             (Set_of_closures.value_slots sc))
        (Set_of_closures.alloc_mode sc)
        function_decls
    in
    all_slot_offsets
      := Slot_offsets.add_set_of_closures !all_slot_offsets ~is_phantom:false
           set_of_closures;
    Static_const.set_of_closures set_of_closures
  | Block (tag, mut, shape, fields) ->
    let fields = List.map (rewrite_simple_with_debuginfo kinds env) fields in
    Static_const.block tag mut shape fields
  | Boxed_float f ->
    Static_const.boxed_float (rewrite_or_variable Float.zero env f)
  | Boxed_float32 f ->
    Static_const.boxed_float32 (rewrite_or_variable Float32.zero env f)
  | Boxed_int32 n ->
    Static_const.boxed_int32 (rewrite_or_variable Int32.zero env n)
  | Boxed_int64 n ->
    Static_const.boxed_int64 (rewrite_or_variable Int64.zero env n)
  | Boxed_nativeint n ->
    Static_const.boxed_nativeint
      (rewrite_or_variable Targetint_32_64.zero env n)
  | Boxed_vec128 n ->
    Static_const.boxed_vec128
      (rewrite_or_variable Vector_types.Vec128.Bit_pattern.zero env n)
  | Immutable_float_block fields ->
    let fields = List.map (rewrite_or_variable Float.zero env) fields in
    Static_const.immutable_float_block fields
  | Immutable_float_array fields ->
    let fields = List.map (rewrite_or_variable Float.zero env) fields in
    Static_const.immutable_float_array fields
  | Immutable_float32_array fields ->
    let fields = List.map (rewrite_or_variable Float32.zero env) fields in
    Static_const.immutable_float32_array fields
  | Immutable_value_array fields ->
    let fields = List.map (rewrite_simple_with_debuginfo kinds env) fields in
    Static_const.immutable_value_array fields
  | Immutable_int32_array fields ->
    let fields = List.map (rewrite_or_variable Int32.zero env) fields in
    Static_const.immutable_int32_array fields
  | Immutable_int64_array fields ->
    let fields = List.map (rewrite_or_variable Int64.zero env) fields in
    Static_const.immutable_int64_array fields
  | Immutable_nativeint_array fields ->
    let fields =
      List.map (rewrite_or_variable Targetint_32_64.zero env) fields
    in
    Static_const.immutable_nativeint_array fields
  | Immutable_vec128_array fields ->
    let fields =
      List.map
        (rewrite_or_variable Vector_types.Vec128.Bit_pattern.zero env)
        fields
    in
    Static_const.immutable_vec128_array fields
  | Empty_array _ | Mutable_string _ | Immutable_string _ -> sc

let rewrite_static_const_or_code kinds env (sc : Static_const_or_code.t) =
  match sc with
  | Code _ -> sc
  | Deleted_code -> sc
  | Static_const sc ->
    Static_const_or_code.create_static_const (rewrite_static_const kinds env sc)

let rewrite_static_const_group kinds env (group : Static_const_group.t) =
  Static_const_group.map ~f:(rewrite_static_const_or_code kinds env) group

let rewrite_set_of_closures bound (env : env) value_slots alloc_mode
    function_decls =
  let slot_is_used slot =
    List.exists
      (fun bv ->
        match
          Hashtbl.find_opt env.uses.uses
            (Code_id_or_name.var (Bound_var.var bv))
        with
        | None | Some Bottom -> false
        | Some Top -> true
        | Some (Fields f) -> Global_flow_graph.Field.Map.mem slot f.fields)
      bound
  in
  let code_is_used bv =
    match
      Hashtbl.find_opt env.uses.uses (Code_id_or_name.var (Bound_var.var bv))
    with
    | None | Some Bottom -> false
    | Some Top -> true
    | Some (Fields f) ->
      Global_flow_graph.Field.Map.mem Code_of_closure f.fields
  in
  let value_slots =
    Value_slot.Map.filter
      (fun slot _ -> slot_is_used (Value_slot slot))
      value_slots
  in
  let open Function_declarations in
  let function_decls =
    List.map2
      (fun bound_var (slot, code_id) ->
        let code_id =
          match code_id with
          | Deleted _ -> code_id
          | Code_id code_id ->
            if code_is_used bound_var
            then Code_id code_id
            else
              let code_metadata = env.get_code_metadata code_id in
              Deleted
                { function_slot_size =
                    Code_metadata.function_slot_size code_metadata;
                  dbg = Code_metadata.dbg code_metadata
                }
        in
        slot, code_id)
      bound
      (Function_slot.Lmap.bindings
         (Function_declarations.funs_in_order function_decls))
  in
  let function_decls =
    Function_declarations.create (Function_slot.Lmap.of_list function_decls)
  in
  Set_of_closures.create ~value_slots alloc_mode function_decls

let simple_in_unboxable env simple =
  Simple.pattern_match
    ~const:(fun _ -> false)
    ~name:(fun name ~coercion:_ ->
      Code_id_or_name.Map.mem
        (Code_id_or_name.name name)
        env.uses.unboxed_fields)
    simple

let get_simple_unboxable env simple =
  Simple.pattern_match
    ~const:(fun _ -> assert false)
    ~name:(fun name ~coercion:_ ->
      Code_id_or_name.Map.find
        (Code_id_or_name.name name)
        env.uses.unboxed_fields)
    simple

let field_kind : Field.t -> _ = function
  | Block (_, kind) -> kind
  | Value_slot vs -> Flambda_kind.With_subkind.kind (Value_slot.kind vs)
  | Function_slot _ | Is_int | Get_tag -> Flambda_kind.value
  | (Code_of_closure | Apply _) as field -> Misc.fatal_errorf "[field_kind] for %a" Field.print field

let rec fold_unboxed_with_kind (f : Flambda_kind.t -> 'a -> 'b -> 'b) (fields : 'a Dep_solver.unboxed_fields Field.Map.t) acc =
  Field.Map.fold (fun field elt acc ->
      match (elt : _ Dep_solver.unboxed_fields) with
      | Not_unboxed elt -> f (field_kind field) elt acc
      | Unboxed fields -> fold_unboxed_with_kind f fields acc
    ) fields acc

(* This is not symmetrical!! [fields1] must define a subset of [fields2], but
   does not have to define all of them. *)
let rec fold2_unboxed_subset (f : 'a -> 'b -> 'c -> 'c)
    (fields1 : 'a Dep_solver.unboxed_fields)
    (fields2 : 'b Dep_solver.unboxed_fields) acc =
  match fields1, fields2 with
  | Not_unboxed x1, Not_unboxed x2 -> f x1 x2 acc
  | Not_unboxed _, Unboxed _ | Unboxed _, Not_unboxed _ ->
    Misc.fatal_errorf "[fold2_unboxed_subset]"
  | Unboxed fields1, Unboxed fields2 ->
    Field.Map.fold
      (fun field f1 acc ->
        let f2 = Field.Map.find field fields2 in
        fold2_unboxed_subset f f1 f2 acc)
      fields1 acc

let rewrite_named kinds env (named : Named.t) =
  let[@local] rewrite_field_access arg field =
    let arg = get_simple_unboxable env arg in
    let var = Field.Map.find field arg in
    let var =
      match var with
      | Dep_solver.Not_unboxed var -> var
      | Dep_solver.Unboxed _ ->
        Misc.fatal_errorf "Trying to bind non-unboxed to unboxed"
    in
    Named.create_simple (Simple.var var)
  in
  match[@ocaml.warning "-4"] named with
  | Simple simple -> Named.create_simple (rewrite_simple kinds env simple)
  | Prim (Unary (Block_load { kind; field; _ }, arg), _dbg)
    when simple_in_unboxable env arg ->
    let kind = Flambda_primitive.Block_access_kind.element_kind_for_load kind in
    let field =
      Global_flow_graph.Field.Block (Targetint_31_63.to_int field, kind)
    in
    rewrite_field_access arg field
  | Prim (Unary (Project_value_slot { value_slot; _ }, arg), _dbg)
    when simple_in_unboxable env arg ->
    rewrite_field_access arg (Global_flow_graph.Field.Value_slot value_slot)
  | Prim (prim, dbg) ->
    let prim = Flambda_primitive.map_args (rewrite_simple kinds env) prim in
    Named.create_prim prim dbg
  | Set_of_closures s -> Named.create_set_of_closures s (* Already rewritten *)
  | Static_consts sc ->
    Named.create_static_consts (rewrite_static_const_group kinds env sc)
  | Rec_info r -> Named.create_rec_info r

let select_list_elements to_select l =
  List.filter_map
    (fun (x, to_select) -> if to_select then Some x else None)
    (List.combine l to_select)

let rewrite_apply_cont_expr kinds env ac =
  let cont = Apply_cont_expr.continuation ac in
  let args = Apply_cont_expr.args ac in
  let args =
    try
      (* only for testing, TODO remove this try/with *)
      let args_to_keep = Continuation.Map.find cont env.cont_params_to_keep in
      select_list_elements args_to_keep args
    with Not_found ->
      Format.eprintf "Missing cont: %a@." Continuation.print cont;
      args
  in
  let args = List.concat_map (fun simple ->
    if simple_in_unboxable env simple then
      let fields = get_simple_unboxable env simple in
            fold_unboxed_with_kind (fun _kind v acc ->
                Simple.var v :: acc)
              fields []
    else
      [rewrite_simple kinds env simple]
    ) args
  in
  Apply_cont_expr.with_continuation_and_args ac cont ~args

let rec rebuild_expr (kinds : Flambda_kind.t Name.Map.t) (env : env)
    (rev_expr : rev_expr) : RE.t =
  let { expr; holed_expr } = rev_expr in
  let expr, free_names =
    match expr with
    | Invalid { message } ->
      Expr.create_invalid (Message message), Name_occurrences.empty
    | Apply_cont ac ->
      let ac = rewrite_apply_cont_expr kinds env ac in
      Expr.create_apply_cont ac, Apply_cont_expr.free_names ac
    | Switch switch ->
      let switch =
        Switch_expr.create
          ~condition_dbg:(Switch_expr.condition_dbg switch)
            (* Scrutinee should never need rewriting, do it anyway for
               completeness *)
          ~scrutinee:(rewrite_simple kinds env (Switch_expr.scrutinee switch))
          ~arms:
            (Targetint_31_63.Map.map
               (rewrite_apply_cont_expr kinds env)
               (Switch_expr.arms switch))
      in
      Expr.create_switch switch, Switch_expr.free_names switch
    | Apply apply ->
      (* CR ncourant: we never rewrite alloc_mode. This is currently ok because
         we never remove begin- or end-region primitives, but might be needed
         later if we chose to handle them. *)
      let call_kind =
        let rewrite_simple = rewrite_simple kinds env in
        match Apply.call_kind apply with
        | Function _ as ck -> ck
        | Method { kind; obj; alloc_mode } ->
          Call_kind.method_call kind ~obj:(rewrite_simple obj) alloc_mode
        | C_call _ as ck -> ck
        | Effect (Perform { eff }) ->
          Call_kind.effect (Call_kind.Effect.perform ~eff:(rewrite_simple eff))
        | Effect (Reperform { eff; cont; last_fiber }) ->
          Call_kind.effect
            (Call_kind.Effect.reperform ~eff:(rewrite_simple eff)
               ~cont:(rewrite_simple cont)
               ~last_fiber:(rewrite_simple last_fiber))
        | Effect (Run_stack { stack; f; arg }) ->
          Call_kind.effect
            (Call_kind.Effect.run_stack ~stack:(rewrite_simple stack)
               ~f:(rewrite_simple f) ~arg:(rewrite_simple arg))
        | Effect (Resume { stack; f; arg; last_fiber }) ->
          Call_kind.effect
            (Call_kind.Effect.resume ~stack:(rewrite_simple stack)
               ~f:(rewrite_simple f) ~arg:(rewrite_simple arg)
               ~last_fiber:(rewrite_simple last_fiber))
      in
      let exn_continuation = Apply.exn_continuation apply in
      let exn_continuation =
        let exn_handler = Exn_continuation.exn_handler exn_continuation in
        let extra_args =
          let selected_extra_args =
            let extra_args = Exn_continuation.extra_args exn_continuation in
            try
              let args_to_keep =
                Continuation.Map.find exn_handler env.cont_params_to_keep
                |> List.tl
                (* This contains the exn argument that is not part of the extra
                   args *)
              in
              select_list_elements args_to_keep extra_args
            with Not_found ->
              (* Not defined in cont_params_to_keep *)
              extra_args
          in
          List.map
            (fun (simple, kind) -> rewrite_simple kinds env simple, kind)
            selected_extra_args
        in
        Exn_continuation.create ~exn_handler ~extra_args
      in
      let args, args_arity, callee =
          (* TODO unbox other args fields *)

          (* List.concat_map (fun simple -> *)
          (*     if simple_in_unboxable env simple then *)
          (*       let fields = get_simple_unboxable env simple in *)
          (*       fold_unboxed_with_kind (fun _kind v acc -> *)
          (*         Simple.var v :: acc) *)
          (*         fields [] *)
          (*     else *)
          (*       [rewrite_simple kinds env simple] *)
          (*   ) (Apply.args apply) *)
          match Apply.callee apply with
          | Some callee when simple_in_unboxable env callee ->
              let fields = get_simple_unboxable env callee in
              let new_args =
                fold_unboxed_with_kind (fun kind v acc ->
                    (kind, Simple.var v) :: acc)
                  fields []
              in
              let args =
                (List.map (rewrite_simple kinds env) (Apply.args apply)) @
                (List.map snd new_args)
              in
              let arity =
                let added_kinds =
                  List.map (fun (kind, _) -> Flambda_kind.With_subkind.anything kind) new_args
                in
                let kinds = Flambda_arity.unarize (Apply.args_arity apply) @ added_kinds in
                let components =
                  List.map (fun k -> Flambda_arity.Component_for_creation.Singleton k) kinds
                in
                Flambda_arity.create [Unboxed_product components]
              in
              args, arity, None
          | None | Some _ ->
              Apply.args apply,
              Apply.args_arity apply,
              rewrite_simple_opt env (Apply.callee apply)
      in
      let apply =
        Apply.create
        (* Note here that callee is rewritten with [rewrite_simple_opt], which
           will put [None] as the callee instead of a dummy value, as a dummy
           value would then be further used in a later simplify pass to refine
           the call kind and produce an invalid. *)
          ~callee
          ~continuation:(Apply.continuation apply) exn_continuation
          ~args
          ~args_arity
          ~return_arity:(Apply.return_arity apply) ~call_kind (Apply.dbg apply)
          ~inlined:(Apply.inlined apply)
          ~inlining_state:(Apply.inlining_state apply)
          ~probe:(Apply.probe apply) ~position:(Apply.position apply)
          ~relative_history:(Apply.relative_history apply)
      in
      Expr.create_apply apply, Apply.free_names apply
  in
  rebuild_holed kinds env holed_expr (RE.from_expr ~expr ~free_names)

and rebuild_function_params_and_body (kinds : Flambda_kind.t Name.Map.t)
    (env : env) (params_and_body : rev_params_and_body) =
  let { return_continuation;
        exn_continuation;
        params;
        body;
        my_closure;
        my_region;
        my_ghost_region;
        my_depth
      } =
    params_and_body
  in
  let body = rebuild_expr kinds env body in
  (* assert (List.exists Fun.id (Continuation.Map.find return_continuation
     env.cont_params_to_keep)); *)
  Function_params_and_body.create ~return_continuation ~exn_continuation params
    ~body:body.expr ~free_names_of_body:(Known body.free_names) ~my_closure
    ~my_region ~my_ghost_region ~my_depth

and bind_fields fields arg_fields hole =
  fold2_unboxed_subset
    (fun var arg hole ->
      let bp =
        Bound_pattern.singleton (Bound_var.create var Name_mode.normal)
      in
      RE.create_let bp (Named.create_simple (Simple.var arg)) ~body:hole)
    fields arg_fields hole

and rebuild_holed (kinds : Flambda_kind.t Name.Map.t) (env : env)
    (rev_expr : rev_expr_holed) (hole : RE.t) : RE.t =
  match rev_expr with
  | Up -> hole
  | Let let_ -> (
    let[@local] erase () = rebuild_holed kinds env let_.parent hole in
    let[@local] default () =
      let subexpr =
        let bp, defining_expr =
          match let_.defining_expr with
          | Named defining_expr -> let_.bound_pattern, defining_expr
          | Static_consts group ->
            let bound_static =
              match let_.bound_pattern with
              | Static l -> l
              | Set_of_closures _ | Singleton _ ->
                (* Bound pattern is static consts, so can't bind something
                   else *)
                assert false
            in
            let bound_and_group =
              List.filter_map
                (fun ((p, e) : Bound_static.Pattern.t * _) ->
                  match p with
                  | Code code_id ->
                    if is_code_id_used env code_id
                    then begin match e with
                      | Code
                          { params_and_body;
                            code_metadata;
                            free_names_of_params_and_body
                          }
                        -> (
                let is_my_closure_used =
                  is_var_used env params_and_body.my_closure
                in
                let params_and_body =
                  rebuild_function_params_and_body kinds env params_and_body
                in
                let code_metadata =
                  if Bool.equal is_my_closure_used
                       (Code_metadata.is_my_closure_used code_metadata)
                  then code_metadata
                  else (
                    assert (not is_my_closure_used);
                    Code_metadata.with_is_my_closure_used is_my_closure_used
                      code_metadata)
                in
                let code =
                  Code.create_with_metadata ~params_and_body ~code_metadata
                    ~free_names_of_params_and_body
                in
                all_code := Code_id.Map.add (Code.code_id code) code !all_code;
                Some (p, Static_const_or_code.create_code code)
              )
                      | Deleted_code ->
                        Some (p, Static_const_or_code.deleted_code)
                      | Static_const _ ->
                        (* Pattern is [Code _], so can't bind static const *)
                        assert false
                    end
                    else (
                      (match e with
                      | Code _ -> ()
                      | Deleted_code -> ()
                      | Static_const _ ->
                        (* Pattern is [Code _], so can't bind static const *)
                        assert false);
                      Some (p, Static_const_or_code.deleted_code))
                  | Block_like sym ->
                    let static_const =
                      match e with
                      | Code _
                      | Deleted_code -> assert false
                      | Static_const static_const -> static_const
                        (* Pattern is [Block_like _], so can't bind code *)
                    in
                    if is_symbol_used env sym then Some (p, Static_const_or_code.create_static_const static_const) else None
                  | Set_of_closures m ->
                    let static_const =
                      match e with
                      | Code _
                      | Deleted_code -> assert false
                      | Static_const static_const -> static_const
                        (* Pattern is [Set_of_closures _], so can't bind code *)
                    in
                    if Function_slot.Lmap.exists
                         (fun _ sym -> is_symbol_used env sym)
                         m
                    then Some (p, Static_const_or_code.create_static_const static_const)
                    else None)
                (List.combine (Bound_static.to_list bound_static) group)
            in
            let bound_static, group = List.split bound_and_group in
            let group =
              Static_const_group.create group
            in
            ( Bound_pattern.static (Bound_static.create bound_static),
              Named.create_static_consts group )
          | Set_of_closures { value_slots; alloc_mode; function_decls } ->
            let bound =
              match let_.bound_pattern with
              | Set_of_closures s -> s
              | Static _ | Singleton _ ->
                (* Pattern is a set of closures *)
                assert false
            in
            let set_of_closures =
              rewrite_set_of_closures bound env value_slots alloc_mode
                function_decls
            in
            let is_phantom =
              Name_mode.is_phantom @@ Bound_pattern.name_mode let_.bound_pattern
            in
            all_slot_offsets
              := Slot_offsets.add_set_of_closures !all_slot_offsets ~is_phantom
                   set_of_closures;
            let_.bound_pattern, Named.create_set_of_closures set_of_closures
        in
        begin
          match let_.bound_pattern with
          | Bound_pattern.Singleton bv
            when Code_id_or_name.Map.mem
                   (Code_id_or_name.var (Bound_var.var bv))
                   env.uses.unboxed_fields -> (
            let to_bind =
              Code_id_or_name.Map.find
                (Code_id_or_name.var (Bound_var.var bv))
                env.uses.unboxed_fields
            in
            match let_.defining_expr with
            | Named named -> (
              match named with
              | Prim (Variadic (Make_block (_kind, _, _), args), _dbg) ->
                Field.Map.fold
                  (fun (field : Global_flow_graph.Field.t) var hole ->
                    let arg =
                      match field with
                      | Block (nth, _kind) ->
                        let arg = List.nth args nth in
                        if simple_in_unboxable env arg
                        then Either.Right (get_simple_unboxable env arg)
                        else Either.Left arg
                      | Is_int -> Either.Left Simple.untagged_const_false
                      | Get_tag ->
                        (* TODO *)
                        assert false
                      | Value_slot _ | Function_slot _ | Code_of_closure
                      | Apply _ ->
                        assert false
                    in
                    match arg with
                    | Either.Left simple ->
                      let var =
                        match var with
                        | Dep_solver.Not_unboxed var -> var
                        | Dep_solver.Unboxed _ ->
                          Misc.fatal_errorf "Trying to unbox non-unboxable"
                      in
                      let bp =
                        Bound_pattern.singleton
                          (Bound_var.create var Name_mode.normal)
                      in
                      RE.create_let bp (Named.create_simple simple) ~body:hole
                    | Either.Right arg_fields ->
                      bind_fields var (Dep_solver.Unboxed arg_fields) hole)
                  to_bind hole
              | Prim
                  ( Unary (Opaque_identity { middle_end_only = true; _ }, arg),
                    _dbg ) ->
                (* XXX TO REMOVE *)
                bind_fields (Dep_solver.Unboxed to_bind)
                  (Dep_solver.Unboxed (get_simple_unboxable env arg))
                  hole
              | Prim (Unary (Block_load { field; kind; _ }, arg), dbg) -> (
                let field =
                  Field.Block
                    ( Targetint_31_63.to_int field,
                      Flambda_primitive.Block_access_kind.element_kind_for_load
                        kind )
                in
                let oarg = arg in
                let arg =
                  Simple.pattern_match arg
                    ~const:(fun _ ->
                      Misc.fatal_error "Loading unboxed from constant")
                    ~name:(fun name ~coercion:_ -> name)
                in
                let arg = Code_id_or_name.name arg in
                match
                  Code_id_or_name.Map.find_opt arg env.uses.unboxed_fields
                with
                | Some arg ->
                  bind_fields (Dep_solver.Unboxed to_bind)
                    (Field.Map.find field arg) hole
                | None ->
                  assert (
                    Code_id_or_name.Map.mem arg env.uses.changed_representation);
                  let arg =
                    Code_id_or_name.Map.find arg env.uses.changed_representation
                  in
                  let arg = Field.Map.find field arg in
                  fold2_unboxed_subset
                    (fun var located_in hole ->
                      let bp =
                        Bound_pattern.singleton
                          (Bound_var.create var Name_mode.normal)
                      in
                      let named =
                        match (located_in : Field.t) with
                        | Block (i, _kind) ->
                          Named.create_prim
                            (Flambda_primitive.Unary
                               ( Block_load
                                   { field = Targetint_31_63.of_int i;
                                     kind =
                                       Flambda_primitive.Block_access_kind
                                       .Values
                                         { tag = Unknown;
                                           size = Unknown;
                                           field_kind =
                                             Flambda_primitive
                                             .Block_access_field_kind
                                             .Any_value
                                         };
                                     mut = Immutable
                                   },
                                 oarg ))
                            dbg
                        | Value_slot _ -> failwith "todo"
                        | Function_slot _ -> failwith "todo"
                        | Is_int | Get_tag | Code_of_closure | Apply _ ->
                          failwith "todo"
                      in
                      RE.create_let bp named ~body:hole)
                    (Dep_solver.Unboxed to_bind) arg hole)
              | Simple arg ->
                bind_fields (Dep_solver.Unboxed to_bind)
                  (Dep_solver.Unboxed (get_simple_unboxable env arg))
                  hole
              | named ->
                Format.printf "BOUM ? %a@." Named.print named;
                assert false)
            | _ -> assert false)
          | Bound_pattern.Singleton bv
            when Code_id_or_name.Map.mem
                   (Code_id_or_name.var (Bound_var.var bv))
                   env.uses.changed_representation -> (
            (* TODO when this block is stored anywhere else, the subkind is no
               longer correct... we need to fix that somehow *)
            match let_.defining_expr with
            | Named
                (Prim
                  (Variadic (Make_block (_kind, _mut, alloc_mode), args), dbg))
              ->
              let fields =
                Code_id_or_name.Map.find
                  (Code_id_or_name.var (Bound_var.var bv))
                  env.uses.changed_representation
              in
              let mp =
                Field.Map.fold
                  (fun f uf mp ->
                    match (f : Field.t) with
                    | Block (i, _kind) -> (
                      let arg = List.nth args i in
                      if simple_in_unboxable env arg
                      then
                        fold2_unboxed_subset
                          (fun ff var mp ->
                            Field.Map.add ff (Simple.var var) mp)
                          uf
                          (Dep_solver.Unboxed (get_simple_unboxable env arg))
                          mp
                      else
                        match uf with
                        | Dep_solver.Not_unboxed ff ->
                          Field.Map.add ff (rewrite_simple kinds env arg) mp
                        | Dep_solver.Unboxed _ ->
                          Misc.fatal_errorf "trying to unbox simple")
                    | Get_tag -> failwith "todo"
                    | Is_int -> failwith "todo"
                    | Value_slot _ | Function_slot _ | Code_of_closure | Apply _
                      ->
                      assert false)
                  fields Field.Map.empty
              in
              let mx = ref 0 in
              Field.Map.iter
                (fun field _ ->
                  match field with
                  | Block (i, kind) ->
                    assert (Flambda_kind.equal kind Flambda_kind.value);
                    mx := max !mx (i + 1)
                  | Get_tag | Is_int | Value_slot _ | Function_slot _
                  | Code_of_closure | Apply _ ->
                    assert false)
                mp;
              let args =
                List.init !mx (fun i ->
                    match
                      Field.Map.find_opt
                        (Field.Block (i, Flambda_kind.value))
                        mp
                    with
                    | None -> Simple.const_zero
                    | Some x -> x)
              in
              let named =
                Named.create_prim
                  (Flambda_primitive.Variadic
                     ( Make_block
                         ( Flambda_primitive.Block_kind.Values
                             ( Tag.Scannable.zero,
                               List.map
                                 (fun _ -> Flambda_kind.With_subkind.any_value)
                                 args ),
                           Immutable,
                           alloc_mode ),
                       args ))
                  dbg
              in
              RE.create_let bp named ~body:hole
            | _ ->
              let defining_expr = rewrite_named kinds env defining_expr in
              RE.create_let bp defining_expr ~body:hole)
          | _ ->
            let defining_expr = rewrite_named kinds env defining_expr in
            RE.create_let bp defining_expr ~body:hole
        end
        [@ocaml.warning "-4"]
      in
      rebuild_holed kinds env let_.parent subexpr
    in
    match let_.bound_pattern with
    | Set_of_closures _ -> default ()
    | Static _ -> default ()
    | Singleton v ->
      let v = Bound_var.var v in
      if is_var_used env v then default () else erase ())
  | Let_cont { cont; parent; handler } ->
    let { bound_parameters; expr; is_exn_handler; is_cold } = handler in
    let parameters_to_keep =
      Continuation.Map.find cont env.cont_params_to_keep
    in
    let cont_handler =
      let handler = rebuild_expr kinds env expr in
      let l = select_list_elements parameters_to_keep (Bound_parameters.to_list bound_parameters) in
      let l = List.concat_map (fun param -> 
        let v = Bound_parameter.var param in
        match Code_id_or_name.Map.find_opt (Code_id_or_name.var v) env.uses.unboxed_fields with
        | None -> [param]
        | Some fields ->
            fold_unboxed_with_kind (fun kind v acc ->
                Bound_parameter.create v (Flambda_kind.With_subkind.anything kind) :: acc)
              fields []
        ) l in
      RE.create_continuation_handler
        (Bound_parameters.create l)
        ~handler ~is_exn_handler ~is_cold
    in
    let let_cont_expr =
      RE.create_non_recursive_let_cont cont cont_handler ~body:hole
    in
    rebuild_holed kinds env parent let_cont_expr
  | Let_cont_rec { parent; handlers; invariant_params } ->
    (* TODO unboxed parameters *)
    let filter_params cont params =
      Bound_parameters.create
        (List.filter
           (fun param -> env.should_keep_param cont (Bound_parameter.var param))
           (Bound_parameters.to_list params))
    in
    let handlers =
      Continuation.Map.mapi
        (fun cont handler ->
          let { bound_parameters; expr; is_exn_handler; is_cold } = handler in
          let bound_parameters = filter_params cont bound_parameters in
          let handler = rebuild_expr kinds env expr in
          RE.create_continuation_handler bound_parameters ~handler
            ~is_exn_handler ~is_cold)
        handlers
    in
    let invariant_params =
      filter_params
        (fst (Continuation.Map.min_binding handlers))
        invariant_params
    in
    let let_cont_expr =
      RE.create_recursive_let_cont ~invariant_params handlers ~body:hole
    in
    rebuild_holed kinds env parent let_cont_expr

type result =
  { body : Expr.t;
    free_names : Name_occurrences.t;
    all_code : Code.t Code_id.Map.t;
    slot_offsets : Slot_offsets.t
  }

let rebuild
    ~(code_deps : Traverse_acc.code_dep Code_id.Map.t)
    ~(continuation_info : Traverse_acc.continuation_info Continuation.Map.t)
    ~fixed_arity_continuations kinds (solved_dep : Dep_solver.result)
    get_code_metadata holed =
  all_slot_offsets := Slot_offsets.empty;
  all_code := Code_id.Map.empty;

  let function_to_unbox code_id (code_dep : Traverse_acc.code_dep) =
    match Code_id_or_name.Map.find_opt
            (Code_id_or_name.var code_dep.my_closure)
            solved_dep.unboxed_fields
    with
    | None -> ()
    | Some _ ->
        Format.eprintf "@.@.XXXX CLOSURE Unbox %a@.@." Code_id.print code_id
  in
  Code_id.Map.iter function_to_unbox code_deps;

  let should_keep_function_param (code_dep : Traverse_acc.code_dep) =
    match Code_id_or_name.Map.find_opt
      (Code_id_or_name.var code_dep.my_closure)
      solved_dep.unboxed_fields
    with
    | None -> (fun _ -> true)
    | Some _ ->
      fun param ->
      let is_var_used = Hashtbl.mem solved_dep.uses (Code_id_or_name.var param) in
      is_var_used
  in
  let function_params_to_keep =
    Code_id.Map.map (fun (code_dep : Traverse_acc.code_dep) ->
        List.map (should_keep_function_param code_dep) code_dep.params)
      code_deps
  in
  let should_keep_function_param code_id =
    match Code_id.Map.find_opt code_id code_deps with
    | None -> (fun _ -> true)
    | Some code_dep -> should_keep_function_param code_dep
  in

  let should_keep_param cont param =
    let keep_all_parameters =
      Continuation.Set.mem cont fixed_arity_continuations
    in
    keep_all_parameters
    ||
    let is_var_used = Hashtbl.mem solved_dep.uses (Code_id_or_name.var param) in
    is_var_used
    ||
    let info = Continuation.Map.find cont continuation_info in
    info.is_exn_handler && Variable.equal param (List.hd info.params)
  in
  let cont_params_to_keep =
    Continuation.Map.mapi
      (fun cont (info : Traverse_acc.continuation_info) ->
        List.map (should_keep_param cont) info.params)
      continuation_info
  in
  let env =
    { uses = solved_dep;
      get_code_metadata;
      cont_params_to_keep;
      should_keep_param;
      function_params_to_keep;
      should_keep_function_param;
    }
  in
  let rebuilt_expr =
    Profile.record_call ~accumulate:true "up" (fun () ->
        rebuild_expr kinds env holed)
  in
  { body = rebuilt_expr.expr;
    free_names = rebuilt_expr.free_names;
    all_code = !all_code;
    slot_offsets = !all_slot_offsets
  }
