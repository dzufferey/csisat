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