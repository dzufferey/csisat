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

(** Satisfiability for difference logic. *)

open   CsisatAst
open   CsisatAstUtil
open   CsisatLIUtils
(**/**)
module Global  = CsisatGlobal
module Message = CsisatMessage
module Utils   = CsisatUtils
module Matrix  = CsisatMatrix
(**/**)

(*TODO 
 * the classical algorithm for DL is to use difference bound matrix (i.e. shortest path algorithms).
 * But we need to do it in an incremental way.
 * For the interpolation, projecting the path on common variable do the job (see MathSat)
 *
 * (1)
 * Floyd-Warshall: http://en.wikipedia.org/wiki/Floyd%E2%80%93Warshall_algorithm
 * works well, and can be used to reconstruct the path (for unsat core).
 * needs also to keep track of the 'strictness of the path'.
 * a distance of 0 means that two nodes should be equal (modulo strictness)
 *
 * (2)
 * For sparse graph Johnson algorithm seems more efficient.
 * http://en.wikipedia.org/wiki/Johnson%27s_algorithm
 * it combines:
 *  http://en.wikipedia.org/wiki/Bellman%E2%80%93Ford_algorithm
 *  http://en.wikipedia.org/wiki/Dijkstra%27s_algorithm
 *  needs Fibonacci heap in the implementation of Dijkstra
 *)

