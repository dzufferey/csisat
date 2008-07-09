(*
 *  CSIsat is an interpolating decision procedure for LA + EUF.
 *  This file is part of CSIsat. 
 *  Copyright (C) 2007-2008  The CSIsat team
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
 *  For information about the CSIsat project,
 *  please visit the CSIsat web page at:
 *  http://www.cs.sfu.ca/~dbeyer/CSIsat/

 *)

external unknown: unit -> int = "unknown"
external satisfiable: unit -> int = "satisfiable"
external unsatisfiable: unit -> int = "unsatisfiable"

external init: unit -> unit = "init"
external reset: unit -> unit = "reset"
external set_seed: int -> unit = "set_seed"
external enable_trace: unit -> unit = "enable_trace"
external adjust: int -> unit = "adjust"
external second: unit -> float = "second"
external add: int -> unit = "add"
external assume: int -> unit = "assume"
external sat: int -> int = "sat"
external deref: int -> int = "deref"
external usedlit: int -> int = "usedlit"
external corelit: int -> int = "corelit"

(*external end_of_proof: unit -> int = "end_of_proof"*)
external get_proof: unit -> int array = "get_proof"
