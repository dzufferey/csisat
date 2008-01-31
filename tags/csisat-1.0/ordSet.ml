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

(***************** ORDSETS ********************)
(* inspired from the Sicstus/SWI prolog library with the same name*)
  
let remove_duplicates lst =
  let rec process last acc lst = match lst with
    | x::xs ->
      begin
        if x <> last then process x (x::acc) xs
        else process last acc xs
      end
    | [] -> List.rev acc
  in
    match lst with
    | x::[] -> [x]
    | x::xs -> process x [x] xs
    | [] -> []

let substract a b =
  let rec process acc a b = match (a,b) with
    | (a,[]) -> (List.rev acc)@a
    | ([],_) -> (List.rev acc)
    | (a::sa, b::bs) ->
      begin
        if a < b then process (a::acc) sa (b::bs)
        else if a > b then process acc (a::sa) bs
        else process acc sa (b::bs)
      end
  in
    process [] a b

let union a b =
  let rec process acc a b = match (a,b) with
    | (a,[]) -> (List.rev acc)@a
    | ([],b) -> (List.rev acc)@b
    | (a::sa, b::bs) ->
      begin
        if a < b then process (a::acc) sa (b::bs)
        else if a > b then process (b::acc) (a::sa) bs
        else process (a::acc) sa bs
      end
  in
    process [] a b

let intersection a b =
  let rec process acc a b = match (a,b) with
    | (_,[]) -> (List.rev acc)
    | ([],_) -> (List.rev acc)
    | (a::sa, b::bs) ->
      begin
        if a < b then process acc sa (b::bs)
        else if a > b then process acc (a::sa) bs
        else process (a::acc) sa bs
      end
  in
    process [] a b

let rec mem el lst = match lst with
  | [] -> false
  | x::xs ->
    begin
        if x < el then mem el xs
        else if x > el then  false
        else true
    end

let list_to_ordSet lst = remove_duplicates (List.sort compare lst)

let cartesian_product l1 l2 =
  List.flatten (List.map (fun x -> List.map (fun y -> (x,y)) l2) l1)
