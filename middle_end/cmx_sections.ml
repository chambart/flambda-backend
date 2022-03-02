(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*                   Mark Shinwell, Jane Street Europe                    *)
(*                                                                        *)
(*   Copyright 2022 OCamlPro SAS                                          *)
(*   Copyright 2022 Jane Street Group LLC                                 *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

open Config
open Cmx_format

type section =
  | Loaded of Obj.t
  | Pending of { byte_offset_in_cmx : int }

type t =
  { channel : in_channel;
    sections : section array
  }

type modname = string

let section_cache : (modname, t) Hashtbl.t = Hashtbl.create 10

let add_unit unit channel ~first_section_offset =
  let sections =
    Array.map
      (fun offset ->
        Pending { byte_offset_in_cmx = offset + first_section_offset })
      unit.ui_section_toc
  in
  if Hashtbl.mem section_cache unit.ui_name
  then Misc.fatal_errorf "Unit loaded multiple time %s" unit.ui_name;
  Hashtbl.add section_cache unit.ui_name { channel; sections }

let read_section_from_cmx_file ~modname ~index =
  match Hashtbl.find_opt section_cache modname with
  | None ->
    Misc.fatal_errorf "Read section %i from an unopened unit %s" index modname
  | Some { sections; channel } -> (
    let num_sections = Array.length sections in
    if index < 0 || index >= num_sections
    then
      Misc.fatal_errorf
        ".cmx file for unit %s only has %d sections, but the section at index \
         %d was requested"
        modname num_sections index
    else
      match sections.(index) with
      | Loaded section_contents -> section_contents
      | Pending { byte_offset_in_cmx } ->
        (* Printf.eprintf "--> seeking to %d\n%!" byte_offset_in_cmx; *)
        seek_in channel byte_offset_in_cmx;
        let section_contents : Obj.t = input_value channel in
        sections.(index) <- Loaded section_contents;
        section_contents)

let close_all () =
  Hashtbl.iter
    (fun _ sections ->
      try close_in sections.channel
      with Sys_error _ ->
        (* In cmxa files, the channel is shared, we might close it multiple
           times *)
        ())
    section_cache;
  Hashtbl.reset section_cache
