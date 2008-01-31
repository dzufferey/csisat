(*  CSIsat: interpolation procedure for LA + EUF
 *  Copyright (C) 2008  The CSIsat team
 *
 *  This program is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation, either version 3 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with this program.  If not, see <http://www.gnu.org/licenses/>.
 *)

let string_list_cat sep lst =
  let buffer = Buffer.create 10 in
  let rec process lst = match lst with
    | x :: [] -> Buffer.add_string buffer x
    | x :: xs -> Buffer.add_string buffer x; Buffer.add_string buffer sep; process xs
    | [] -> ()
  in
    process lst;
    Buffer.contents buffer

(*lst has at least one element*)
let min_of_list query_fct lst =
  let min_term = ref (List.hd lst) in
  let min_val = ref (query_fct (List.hd lst)) in
    List.iter (fun x ->
        let v = query_fct x in
          if v < !min_val then
            begin
              min_term := x;
              min_val := v
            end
      ) lst;
    !min_term

let remove_some lst =
  List.map
    (fun x -> match x with
      | Some x -> x
      | None -> failwith "remove_some found a None"
    ) lst

(*take the n first element of the list*)
let split_list n lst =
  let acc = ref [] in
  let rec process n lst = match lst with
    | (x::xs) as lst ->
      if n > 0 then
        begin
          acc := x::!acc;
          process (n-1 ) xs
        end
      else lst
    | [] -> []
  in
  let tail = process n lst in
    (List.rev !acc, tail)

let rec map_filter fct lst = match lst with
  | x::xs ->
    begin
      match fct x with
      | Some r -> r::(map_filter fct xs)
      | None -> map_filter fct xs
    end
  | [] -> []

(*from a list of edges (pairs) to a adjacency hashtbl*)
let edges_to_graph edges =
  let graph = Hashtbl.create 53 in
    List.iter 
      ( fun (x,y) ->
        let already =
          try Hashtbl.find graph x
          with Not_found -> []
        in
          Hashtbl.replace graph x (y::already);
          if not (Hashtbl.mem graph y) then Hashtbl.add graph y []
      ) edges;
    graph

let edges_to_graph_not_directed edges =
  let graph = Hashtbl.create 53 in
    List.iter 
      ( fun (x,y) ->
        let alreadyx =
          try Hashtbl.find graph x
          with Not_found -> []
        in
        let alreadyy =
          try Hashtbl.find graph y
          with Not_found -> []
        in
          Hashtbl.replace graph x (y::alreadyx);
          Hashtbl.replace graph y (x::alreadyy)
      ) edges;
    graph
