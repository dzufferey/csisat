(*
 *  CSIsat is an interpolating decision procedure for LA + EUF.
 *  This file is part of CSIsat. 
 *
 *  Copyright (C) 2007-2008  Dirk Beyer and Damien Zufferey.
 *  All rights reserved.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 *
 *
 *  CSIsat web page:
 *    http://www.cs.sfu.ca/~dbeyer/CSIsat/
 *)

(** General methods that are mostly independent from other parts.
 *)

(**/**)
module OrdSet = CsisatOrdSet
(**/**)

module Int =
  struct
    type t = int
    let compare = compare
  end
module IntSet = Set.Make(Int)
module IntMap = Map.Make(Int)

module StringSet = Set.Make(String)
module StringMap = Map.Make(String)

(** ugly method to search in an IntSet *)
let find_in_IntSet query set =
  let elt = ref None in
  let res =  IntSet.exists
    (fun x ->
      if query x then
        begin
          elt := Some x;
          true
        end
      else false
    ) set
  in
    if res then
      begin
        match !elt with
        | Some x -> x
        | None -> failwith "Utils, find_in_IntSet: found, but not found ?!"
      end
    else raise Not_found

(*
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
*)

(** Print a float and removes trailing '.'.
 *)
let my_string_of_float flt =
  let (f,i) = modf flt in
    if f = 0.0 then string_of_int (int_of_float i)
    else string_of_float flt

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
let remove_some_once x = match x with
  | Some x -> x
  | None -> failwith "remove_some found a None"
let remove_some lst = List.map remove_some_once lst

(** Applies fct to some, returns default otherwise *)
let maybe fct default opt = match opt with
  | Some x -> fct x
  | None -> Lazy.force default

let uniq l =
  List.fold_right
    (fun elt acc -> if List.mem elt acc then acc else elt::acc)
    l
    []

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

let rec partition_while fct lst = match lst with
  | x::xs -> if fct x then let (ys,rest) = partition_while fct xs in (x::ys, rest) else ([],x::xs)
  | [] -> ([], [])
let rec take_while fct lst = match lst with
  | x::xs -> if fct x then x::(take_while fct xs) else []
  | [] -> []
let rec drop_while fct lst = match lst with
  | x::xs -> if fct x then drop_while fct xs else x::xs
  | [] -> []

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

let get_scc_undirected_graph edges =
  let graph = edges_to_graph_not_directed edges in
  let rec get_class_of x =
    if Hashtbl.mem graph x then
      begin
        let neighbours = OrdSet.list_to_ordSet (Hashtbl.find graph x) in
          Hashtbl.remove graph x;
          List.fold_left (fun acc x -> OrdSet.union acc (get_class_of x)) [x] neighbours
      end
    else
      []
  in
  let keys = Hashtbl.fold (fun k _ acc -> k::acc) graph [] in
  let ccs = List.map get_class_of keys in
    List.filter (fun lst -> lst <> []) ccs

let rec path_to_edges lst = match lst with
  | x :: y :: xs -> (x,y) :: path_to_edges (y::xs)
  | _ -> []

(* immutable (add/remove creates a new graph) *)
module UndirectedIntGraph :
  sig
    type t
    val to_string: t -> string
    val get: t -> int -> IntSet.t
    val add: t -> int -> int -> t 
    val remove: t -> int -> int -> t
    val create: (int * int) list -> t
    val merge: t -> t -> t
    val empty: t
    val shortest_path: t -> int -> int -> int list
    val get_scc: t -> IntSet.t list
    val project_scc: t -> int list -> IntSet.t list
  end
=
  struct
    type t = IntSet.t IntMap.t
    
    let to_string t =
      let buffer = Buffer.create 1000 in
      let add = Buffer.add_string buffer in
        IntMap.iter
          (fun k v ->
            let succ = String.concat ", " (List.map string_of_int (IntSet.elements v)) in
            add ((string_of_int k) ^ " -> " ^ succ ^ "\n") )
          t;
        Buffer.contents buffer

    let get graph x =
      if IntMap.mem x graph
      then IntMap.find x graph
      else IntSet.empty
    
    let add graph x y =
      let alreadyx = get graph x in
      let alreadyy = get graph y in
      let graph'  = IntMap.add x (IntSet.add y alreadyx) graph  in
      let graph'' = IntMap.add y (IntSet.add x alreadyy) graph' in
        graph''

    let remove graph x y =
      let alreadyx = get graph x in
      let alreadyy = get graph y in
      let graph'  = IntMap.add x (IntSet.remove y alreadyx) graph  in
      let graph'' = IntMap.add y (IntSet.remove x alreadyy) graph' in
        graph''

    let create edges =
      List.fold_left
        (fun graph (x,y) -> add graph x y)
        IntMap.empty
        edges
    
    let merge graph1 graph2 =
      IntMap.fold
        (fun x set acc -> IntMap.add x (IntSet.union set (get acc x)) acc)
        graph1
        graph2

    let empty = IntMap.empty

    let get_scc graph =
      let rec get_class_of graph x =
        if IntMap.mem x graph then
          begin
            let neighbours = get graph x in
            let graph = IntMap.remove x graph in
              IntSet.fold
                (fun x (acc_g, acc_c) ->
                  let g, c = get_class_of acc_g x in
                    (g, IntSet.union acc_c c)
                )
                neighbours
                (graph, IntSet.singleton x)
          end
        else
          (graph, IntSet.empty)
      in
      let keys = IntMap.fold (fun k _ acc -> k::acc) graph [] in
      let _, ccs =
        List.fold_left
          (fun (acc_g, acc_cls) k -> let g, cls = get_class_of acc_g k in (g, cls::acc_cls))
          (graph, [])
          keys
      in
        List.filter (fun x -> not (IntSet.is_empty x)) ccs

    let project_scc graph lst =
      let ccs = get_scc graph in
      let to_keep = List.fold_left (fun acc x -> IntSet.add x acc) IntSet.empty lst in
      let ccs2 = List.map (IntSet.inter to_keep) ccs in
        List.filter (fun x -> not (IntSet.is_empty x)) ccs2


    (* since the graph is not weigted, a BFS should be sufficient ?? *)
    let shortest_path graph a b =
      (* print_endline ("shortest_path from " ^(string_of_int a)^ " to " ^ (string_of_int b));
      IntMap.iter (fun k v -> print_endline ((string_of_int k) ^ " -> " ^ (String.concat ", " (List.map string_of_int (IntSet.elements v))))) graph; *)
      let visited = ref IntSet.empty in
      let to_process = Queue.create () in
      let pred = Hashtbl.create 100 in
      let rec find_b () =
        let n = Queue.take to_process in
          if IntSet.mem n !visited then find_b ()
          else if n = b then
            begin
              (*get path to a*)
              let rec get_path current acc =
                (*print_endline ("get_path from " ^ (string_of_int current)^ " to " ^ (string_of_int a));*)
                if current = a then a::acc
                else get_path (Hashtbl.find pred current) (current::acc)
              in
                get_path b []
            end
          else
            begin
              visited := IntSet.add n !visited;
              IntSet.iter
                (fun m ->
                  Queue.add m to_process;
                  if not (Hashtbl.mem pred m) then Hashtbl.add pred m n
                )
                (get graph n);
                find_b ()
            end
      in
        Queue.add a to_process;
        find_b ()

  end

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
let power base exponent =
  assert (exponent >= 0);
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

let is_integer n =
  let (f,i) = modf n in f = 0.0

let round n =
  let (f,i) = modf n in
    if f < (-0.5) then i -. 1.
    else if f >= 0.5 then i +. 1.
    else i

let cartesian_product l1 l2 =
  List.flatten (List.map (fun x -> List.map (fun y -> (x,y)) l2) l1)

(*does not include max*)
let range min max =
  let rec process acc curr =
    if curr >= max then List.rev acc
    else process (curr::acc) (curr + 1)
  in
    process [] min

(** closed and finite intervals of integer *)
module Interval =
  struct
    type t = int * int

    let is_empty (a,b) = a > b
    
    let mem x (a,b) = x >= a && x <= b

    let inter (a,b) (c,d) =
      let a' = max a c in
      let b' = min b d in
        assert(a' <= b');
        (a', b')

    (** only for intervals with non empty intersection*)
    let union (a,b) (c,d) =
      let a' = min a c in
      let b' = max b d in
        assert(not (is_empty (inter (a,b) (c,d))));
        (a', b')

    let min (a,b) = a

    let max (a,b) = b

  end

(** Transpose a list of list *)
let rec transpose m =
  if List.mem [] m then []
  else (List.map List.hd m) :: transpose (List.map List.tl m)

(** [a;b;c;...] => [(a,b);(b,c);...]*)
let pairs_of_list lst =
  assert(List.length lst >= 2);
  let rec process acc lst = match lst with
    | x::y::xs -> process ((x,y)::acc) (y::xs)
    | x::[] -> List.rev acc
    | [] -> failwith "Utils.pairs_of_list ??"
  in
    process [] lst
