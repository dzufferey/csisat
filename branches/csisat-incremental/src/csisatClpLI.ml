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

(** This file is based on Rybalchenko et al. "Constraint Solving for Interpolation".
 * http://www.mpi-sws.mpg.de/~rybal/papers/vmcai07-constraints-for-interpolation.pdf
 *)

open   CsisatAst
open   CsisatAstUtil
open   CsisatLIUtils
(**/**)
module Global  = CsisatGlobal
module Message = CsisatMessage
module Utils   = CsisatUtils
module Matrix  = CsisatMatrix
(**/**)

(** Kind of lambda *)
type l_type = LT | LEQ | EQ

(** L and T correspond to additional constraints used to remove the case split of the algorithm. *)
type l_info = L of int (** index *)
            | T of int (** index *)
            | Lambda of int * int * l_type (** index, block (i.e position in the input list), type *)

let index_of info = match info with
  | L i | T i | Lambda (i,_,_) -> i
let block_of info = match info with
  | Lambda (_,b,_) -> b
  | _ -> failwith "ClpLI: block_of on L or T"

let lambda_to_string l = match l with
  | L i ->             "L has index "^(string_of_int i)
  | T i ->             "T has index "^(string_of_int i)
  | Lambda(i,b,LT) ->  "L"^(string_of_int i)^" of block "^(string_of_int b)^" with <"
  | Lambda(i,b,LEQ) -> "L"^(string_of_int i)^" of block "^(string_of_int b)^" with <="
  | Lambda(i,b,EQ) ->  "L"^(string_of_int i)^" of block "^(string_of_int b)^" with ="

let print_lambda lambda = Message.print Message.Debug (lazy(lambda_to_string lambda))
let print_lambdas lambdas = List.iter print_lambda lambdas

(** Separates strict, non-strict, and equlity constraints *)
let split_eq_lt pred =
  let rec process (accLt, accLeq, accEq) pred = match pred with
    | And [] -> (accLt, (Leq(Constant 0.0, Constant 1.0))::accLeq, accEq)
    | And lst -> List.fold_left process (accLt, accLeq, accEq) lst
    | Leq _ as leq -> (accLt, leq::accLeq, accEq)
    | Lt  _ as lt  -> (lt::accLt, accLeq, accEq)
    | Eq _ as eq -> (accLt, accLeq, eq::accEq)
    | True -> (accLt, (Leq(Constant 0.0, Constant 1.0))::accLeq, accEq)
    | False -> (accLt, (Leq(Constant 1.0, Constant 0.0))::accLeq, accEq)
    | _ -> failwith "split_eq_lt: supports only And,Lt,Leq,Eq"
  in
  let (lt,leq,eq) = process ([],[],[]) pred in
    (List.rev lt, List.rev leq, List.rev eq)

(** Prepare the constraints ->  split eq/leq/lt and creates a matrix/vector. *)
let prepare vars cnf =
  let (lt,leq,eq) = split_eq_lt cnf in
  let size_lt = List.length lt in
  let size_leq = List.length leq in
  let size_eq = List.length eq in
  let (mat,vect) = conj_to_matrix (lt @ leq @ eq) vars in
    (size_lt,size_leq,size_eq,mat,vect)

(** use this method to prepare the argument of extract_constraints*)
let prepare2 cnf =
  let (lt,leq,eq) = split_eq_lt cnf in
  let size_lt = List.length lt in
  let size_leq = List.length leq in
  let size_eq = List.length eq in
  let preds = Array.of_list (lt @ leq @ eq) in
    (size_lt,size_leq,size_eq,preds)

(** compute i = λA and d = λa *)
let compute_interpolant vars_size blocks results =
  let i_acc = Array.make vars_size 0.0 in
  let d_acc = ref 0.0 in
  let rec process blocks results acc = match (blocks,results) with
    | ((size_lt,size_leq,size_eq,mat,vect)::bs,(nonstrict,result)::rs) ->
      begin
        Message.print Message.Debug (lazy("result = "^(Matrix.string_of_row_vector result)^"^T"));
        Message.print Message.Debug (lazy("matrix =\n"^(Matrix.string_of_matrix mat)));
        let i = Matrix.vector_times_matrix result mat in
        let i = Array.map (fun x -> if (abs_float x) < !solver.solver_error then 0.0 else x) i in
          for k = 0 to vars_size -1 do
            i_acc.(k) <- i_acc.(k) +. i.(k)
          done;
          Message.print Message.Debug (lazy("I: "^(String.concat ", " (Array.to_list (Array.map string_of_float i_acc)))));
          let d = Matrix.row_vect_times_col_vect result vect in
          let d = if (abs_float d) < !solver.solver_error then 0.0 else d in
            d_acc := d +. !d_acc;
            let strictness = if nonstrict then LEQ else LT in
              process bs rs ((Array.copy i_acc, strictness, !d_acc)::acc)
      end
    | (_,[]) -> List.rev acc
    | _ -> failwith "compute_interpolant: match error/too much result"
  in
    process blocks results [] 

(* a Farcas/Motzkin prrof of unsat for a system of linear inequalities *)
module Proof =
  struct
    type lambdas_def = l_info list
    type lambdas_val = float array * int (*value of lambdas + number of non strict interpolant (λ index)*)
    type constraints = predicate array
    (*the index in the λ gives the position in the arrays *)
    type t = lambdas_def * lambdas_val * constraints

    let to_string proof =
      let (lambdas_def, (lambdas_val, non_strict), constraints) = proof in
      let buffer = Buffer.create 1000 in
      let add str = Buffer.add_string buffer str; Buffer.add_char buffer '\n' in
        add "Lambda defs:";
        List.iter (fun l -> add (lambda_to_string l)) lambdas_def;
        add "Lambda values:";
        Array.iter (fun f -> add (string_of_float f)) lambdas_val;
        add ("Non strict up to "^(string_of_int non_strict));
        add "Constraints:";
        Array.iter (fun f -> add (print_pred f)) constraints;
        Buffer.contents buffer

    (** Computes interpolants from the proof
     * (1) get the variables
     * (2) transform the blocks into matrixes
     * (3) mutliply the λ with the matrixes to get the interpolants
     * (4) set the strictness of the interpolants *)
    let interpolate (proof: t) =
      let (lambdas_def, (lambdas_val, non_strict), constraints) = proof in
      (* (1) *)
      let vars_set =
        List.fold_left
          (fun acc x -> ExprSet.add x acc)
          ExprSet.empty
          (List.flatten (Array.to_list (Array.map collect_li_vars constraints)))
      in
      let vars = exprSet_to_ordSet vars_set in
      let nb_vars = List.length vars in
      (* (2) *) (* group constraints by blocks *)
      let max_block = block_of (List.hd (List.rev lambdas_def)) in
      let blocks_of_lambdas =
        List.map
          (fun i -> List.filter (fun l -> (block_of l) = i) lambdas_def)
          (Utils.range 0 max_block) (*this does not return the last λs (they are not needed since we want n-1 interpolant)*)
      in
      let blocks_of_indexes = List.map (List.map index_of) blocks_of_lambdas in
      let blocks_of_constraints = List.map (fun idxs -> And (List.map (fun i -> constraints.(i)) idxs)) blocks_of_indexes in
      let matrixes = List.map (prepare vars) blocks_of_constraints in
      (* (3) *)
      let rec split_lambdas cur_block start len acc lambdas = match lambdas with
        | (Lambda (index,block,_))::xs ->
          begin
            if block <> cur_block then
              begin
                split_lambdas block (start+len) 0 ((cur_block < non_strict, (Array.sub lambdas_val start len))::acc) xs
              end
            else split_lambdas cur_block start (len+1) acc xs
          end
        | x::xs -> failwith "interpolate: expect only lambda's"
        | [] -> List.rev acc
      in
      let result = split_lambdas 0 0 0 [] lambdas_def in
      let is_ds = compute_interpolant nb_vars matrixes result in
      (* (4) *)
      let interpolants = List.map (fun (i,strictness,d) ->
            begin
              let expr = Matrix.symbolic_vector_multiplication i vars in
                Message.print Message.Debug (lazy("left part is: "^(print_expr expr)));
              let full_ans = match strictness with
                | LT -> Lt (expr, Constant d)
                | LEQ -> Leq(expr, Constant d)
                | EQ -> failwith "interpolate_clp: invalide strictness -> EQ"
              in
                simplify full_ans
            end
            ) is_ds
      in
        interpolants

    let unsat_core (proof: t) =
      let (lambdas_def, (lambdas_val, non_strict), constraints) = proof in
      let part_of_core = List.filter (fun l -> lambdas_val.(index_of l) <> 0.0) lambdas_def in
        List.map (fun l -> constraints.(index_of l)) part_of_core
      
  end

(** Fills the Main matrix with the different sub-matrixes.
 *  Assume the GLPK problem is big enough.
 *  Implicitely preform the problem transposition.*)
let rec fill_glpk_problem lp nb_vars block index acc lst = match lst with
  | (size_lt,size_leq,size_eq,mat,_)::xs ->
    begin
      Message.print Message.Debug (lazy("\nMatrix of block "^(string_of_int block)^" :\n"^(Matrix.string_of_matrix mat)));
      let new_acc = ref acc in
      let new_index = ref index in
        (*!! at this point the transposition of the matrix is implicit (by filling row->col)!!*)
        Camlglpk.add_col lp (Array.length mat);
        for i = 0 to  size_lt - 1 do
          Camlglpk.set_mat_col lp !new_index nb_vars mat.(i);
          Camlglpk.set_col_bnd_lower lp !new_index 0.0; (*lambda >= 0*)
          new_acc := (Lambda (!new_index, block, LT))::(!new_acc);
          new_index := !new_index + 1
        done;
        for i = size_lt to  size_lt + size_leq - 1 do
          Camlglpk.set_mat_col lp !new_index nb_vars mat.(i);
          Camlglpk.set_col_bnd_lower lp !new_index 0.0; (*lambda >= 0*)
          new_acc := (Lambda (!new_index, block, LEQ))::(!new_acc);
          new_index := !new_index + 1
        done;
        for i = size_lt + size_leq to  size_lt + size_leq + size_eq - 1 do
          Camlglpk.set_mat_col lp !new_index nb_vars mat.(i);
          Camlglpk.set_col_bnd_free lp !new_index;
          new_acc := (Lambda (!new_index, block, EQ))::(!new_acc);
          new_index := !new_index + 1
        done;
        fill_glpk_problem lp nb_vars (block + 1) !new_index !new_acc xs
    end
  | [] -> acc

(* to make a proof: the lambda part *)
let rec extract_lamdas_def block index acc lst = match lst with
  | (size_lt,size_leq,size_eq,mat,_)::xs ->
    begin
      let new_acc = ref acc in
      let new_index = ref index in
        for i = 0 to  size_lt - 1 do
          new_acc := (Lambda (!new_index, block, LT))::(!new_acc);
          new_index := !new_index + 1
        done;
        for i = size_lt to  size_lt + size_leq - 1 do
          new_acc := (Lambda (!new_index, block, LEQ))::(!new_acc);
          new_index := !new_index + 1
        done;
        for i = size_lt + size_leq to  size_lt + size_leq + size_eq - 1 do
          new_acc := (Lambda (!new_index, block, EQ))::(!new_acc);
          new_index := !new_index + 1
        done;
        extract_lamdas_def (block + 1) !new_index !new_acc xs
    end
  | [] -> List.rev acc

let rec extract_constraints block index acc lst = match lst with
  | (size_lt,size_leq,size_eq,mat)::xs ->
    begin
      let new_acc = ref acc in
      let new_index = ref index in
        for i = 0 to  size_lt - 1 do
          new_acc := mat.(i)::(!new_acc);
          new_index := !new_index + 1
        done;
        for i = size_lt to  size_lt + size_leq - 1 do
          new_acc := mat.(i)::(!new_acc);
          new_index := !new_index + 1
        done;
        for i = size_lt + size_leq to  size_lt + size_leq + size_eq - 1 do
          new_acc := mat.(i)::(!new_acc);
          new_index := !new_index + 1
        done;
        extract_constraints (block + 1) !new_index !new_acc xs
    end
  | [] -> Array.of_list (List.rev acc)

(** extract the lambdas value for the proof *)
let extract_lamdas_val lp lambdas_def =
  let rec count_non_strict results lambdas = match lambdas with
    | (Lambda (index,block,LT))::xs -> if results.(index) > !solver.solver_error then block else count_non_strict results xs
    | (Lambda (_,_,_))::xs -> count_non_strict results xs
    | x::xs -> failwith "extract_lamdas_val: expect only lambda's"
    | [] -> failwith "extract_lamdas_val: reached the end before a non-0 \\^lt"
  in
  let value = !solver.obj_val lp in
    if value >= (2.0 -. !solver.solver_error) then raise SAT
    else
      begin
        let last_lambda_index = List.length lambdas_def in
        let result = Array.make last_lambda_index 0.0 in
          !solver.cols_primal lp last_lambda_index result;
          (*the solver precision is 10e-7 => filter all term that are less than !solver.solver_error*)
          Array.iteri (fun i x -> if (abs_float x) < !solver.solver_error then result.(i) <- 0.0) result;
          let count = (*count is the number of non-strict interpolant*)
            if value < (1.0 -. !solver.solver_error) then last_lambda_index (*is bigger than the number of interpolant, but not important*)
            else count_non_strict result lambdas_def
          in
            (result, count)
      end

(** Collects the a's for minimization constraints*)
let rec get_all_as index target_array lst = match lst with
  | (_,_,_,_,vect)::xs ->
    begin
      let size = Array.length vect in
        Array.blit vect 0 target_array index size;
        get_all_as (index + size) target_array xs
    end
  | [] -> ()

(** For the 'strictness' constraint*)
let rec get_lt_lambdas target_array lambdas = match lambdas with
  | (Lambda (i,_,LT))::xs ->
      target_array.(i) <- (-1.0);
      get_lt_lambdas target_array xs
  | _::xs -> get_lt_lambdas target_array xs
  | [] -> ()
    
(** Make a Farcas/Motzkin proof of unsat.
 *  Assumes non trivial case *)
let mk_proof lst =
  Message.print Message.Debug (lazy("ClpLI mk_proof called: " ^ (String.concat ", " (List.map print lst))));
  let vars_set = List.fold_left (fun acc x -> ExprSet.add x acc) ExprSet.empty (List.flatten (List.map collect_li_vars lst)) in
  let vars = exprSet_to_ordSet vars_set in
  let nb_vars = List.length vars in
    Message.print Message.Debug (lazy("Variables are: " ^ (String.concat ", " (List.map print_expr vars))));
    assert (Global.is_off_assert() || nb_vars > 0 );
    let prepared = List.map (prepare vars) lst in
    let lp = Camlglpk.create () in
      Camlglpk.add_row lp nb_vars;
      for i = 0 to nb_vars -1 do (*Sum l*A = 0*)
        Camlglpk.set_row_bnd_fixed lp i 0.0
      done;
      let lambda1 = fill_glpk_problem lp nb_vars 0 0 [] prepared in
      let last_lambda_index = index_of (List.hd lambda1) in
      let l_index = last_lambda_index + 1 in
      let t_index = last_lambda_index + 2 in
      let lambda2 = (L l_index)::lambda1 in
      let lambdas = (T t_index)::lambda2 in
        print_lambdas lambdas;
        Camlglpk.add_col lp 2;(* for L and T *)
        Camlglpk.set_col_bnd_upper lp l_index 1.0; (*L <= 1*)
        Camlglpk.set_col_bnd_lower lp t_index 0.0; (*T >= 0*)
        Camlglpk.add_row lp 2;(* min cstr *)
        let all_as = Array.make (last_lambda_index + 3) 0.0 in
          get_all_as 0 all_as prepared;
          all_as.(l_index) <- (-1.0);
          all_as.(t_index) <- (-1.0);
          Camlglpk.set_mat_row lp  nb_vars  (Array.length all_as) all_as;
          Camlglpk.set_row_bnd_upper lp nb_vars (-2.0);
          Array.fill all_as 0 (Array.length all_as) 0.0;
          get_lt_lambdas all_as lambdas;
          all_as.(l_index) <- 1.0;
          Camlglpk.set_mat_row lp (nb_vars + 1) (Array.length all_as) all_as;
          Camlglpk.set_row_bnd_upper lp (nb_vars + 1) (0.0);
          (*objective function*)
          Camlglpk.set_minimize lp;
          Camlglpk.set_obj_coef lp t_index 1.0;
          if !solver.solve lp then
            begin
              let lambdas_def = List.rev lambda1 in
              let constraints = extract_constraints 0 0 [] (List.map prepare2 lst) in
              let lambas_val = extract_lamdas_val lp (List.rev lambda1) in
                 Camlglpk.delete lp;
                 (lambdas_def, lambas_val, constraints)
            end
          else
            begin 
              Camlglpk.dump_problem lp;
              Camlglpk.delete lp;
              raise LP_SOLVER_FAILURE
            end
        
(** compute a series of |lst| -1 (inductive) interpolant *)
let interpolate_clp lst =
  Message.print Message.Debug (lazy("interpolate_clp called: " ^ (String.concat ", " (List.map print lst))));
  let proof = mk_proof lst in
    Message.print Message.Debug (lazy("interpolate_clp proof:\n" ^ (Proof.to_string proof)));
    Proof.interpolate proof

(** Returns an over-approximation of the unsat core for a formula.
 *  This method is based on Motzkin's transposition Theorem.
 *  Assume the formula is unsat. *)
let unsat_core lst =
  Message.print Message.Debug (lazy("unsat_core_clp called: " ^ (String.concat ", " (List.map print lst))));
  let proof = mk_proof lst in
    Message.print Message.Debug (lazy("unsat_core_clp proof:\n" ^ (Proof.to_string proof)));
    Proof.unsat_core proof
