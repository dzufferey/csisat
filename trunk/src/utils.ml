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

(** General methods that are independent from other parts.
 *)

(** Concatenates a list of string, adding a separator between 2 elements.
 * @param sep the separator
 * @param lst the list to concatenate
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

(** Returns the minimum x of query_fct(x) for x in lst.
 * Assume that lst has at least one element.
 *)
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

(** Removes the Some of an option *)
let remove_some lst =
  List.map
    (fun x -> match x with
      | Some x -> x
      | None -> failwith "remove_some found a None"
    ) lst

(** splits a list after position n.*)
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

(** map + keep only elements y where fct(x) = Some(y)*)
let rec map_filter fct lst = match lst with
  | x::xs ->
    begin
      match fct x with
      | Some r -> r::(map_filter fct xs)
      | None -> map_filter fct xs
    end
  | [] -> []

let rev_flatten lst = 
  List.fold_left (fun acc x -> List.rev_append x acc) [] lst

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

(* build the list of primes *)
let prime_list n =
  let rec is_prime lst_prime x =
    match lst_prime with
    | p::ps ->
      if (x mod p) = 0 then
        false
      else
		    if p*p > x then
		      true
		    else
          is_prime ps x
    | [] -> true
  in
    let rec build_list acc i =
      if i > n then
        acc
      else
        begin
          if is_prime acc i then
            build_list (i::acc) (i+1)
          else
            build_list acc (i+1)
        end
    in
      build_list [] 2

(** gives the prime number decomposition of a number.
 * assume n is positive.
 *)
let factorise n = 
  if n = 1 then [1] (*!!!*)
  else
    begin
      let primes = List.rev (prime_list (int_of_float (sqrt (float_of_int n)))) in
        let c = ref n in
        let rec iter acc x =
          match x with
          | [] -> acc
          | y::ys ->
              if (!c mod y) = 0 then
                begin
                  c := !c / y;
                  iter (y::acc) x
                end
              else
                iter acc ys
         in
          let result = iter [] primes in
            if !c <> 1 then
              !c :: result
            else
              result
    end

(** power of integers.
 *  Assume exponent to be >= 0
 *)
let rec power base exponent =
  let rec pow acc base exponent = 
    if exponent = 0 then acc
    else if (exponent mod 2) = 0 then pow acc (base * base) (exponent / 2)
    else
      begin
       assert ((exponent mod 2) = 1); 
       pow (acc * base) base (exponent -1)
      end
  in
    pow 1 base exponent

let round n =
  let (f,i) = modf n in
    if f < (-0.5) then i -. 1.
    else if f >= 0.5 then i +. 1.
    else i

let cartesian_product l1 l2 =
  List.flatten (List.map (fun x -> List.map (fun y -> (x,y)) l2) l1)
