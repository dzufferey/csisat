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

open Ast

module CharSet = Set.Make(Char)
(*****************************************************************************)
(*************************          PARSER          **************************)
(*****************************************************************************)
(*let's go for a simple top down parsing*)

(*control character*)
let _LBRACK = '['
let _RBRACK = ']'
let _LPAREN = '('
let _RPAREN = ')'
let _SEMICOLON = ';'
let _PLUS = '+'
let _TIMES = '*'
let _DASH = '-' (* for -> *)
let _AND = '&'
let _OR = '|'
let _EQ = '='
let _NOT = '~'
let _LEQ = '<' (* for <= *)
let _EOF = char_of_int 0

(*whitespace characters*)
let whitespace = 
  CharSet.add ' ' (
  CharSet.add '\n' (
  CharSet.add '\r' (
  CharSet.add '\t' (
  CharSet.empty ))))

(*control characters*)
let ctrlChar =
  CharSet.add _LBRACK (
  CharSet.add _RBRACK (
  CharSet.add _LPAREN(
  CharSet.add _RPAREN (
  CharSet.add _SEMICOLON (
  CharSet.add _PLUS (
  CharSet.add _TIMES (
  CharSet.add _DASH (
  CharSet.add _AND (
  CharSet.add _OR (
  CharSet.add _EQ (
  CharSet.add _NOT (
  CharSet.add _LEQ (
  CharSet.empty )))))))))))))

(*all is encapsulated in the function => no side effect*)
let parse_foci input_string =
  let in_stream = Stream.of_string input_string in
      
  let current = ref ' ' in

  let next_char () =
    try
      current := Stream.next in_stream;
    with Stream.Failure -> current := _EOF in

  let next_token () = 
    next_char();
    while CharSet.mem !current whitespace do
      next_char();
    done in

  (*to use after buffer_to_next_ws
    when the current char can already be the next tocken
  *)
  let next_token2 () =
    while CharSet.mem !current whitespace do
      next_char();
    done in

  (*return the chars until the next '
    takes at least one char*)
  let buffer_to_next_little_thing_above () =
    Message.print Message.Debug (lazy "buffer_to_next_little_thing_above");
    let buffer = Buffer.create 0 in
      Buffer.add_char buffer !current;
      next_char();
      while not (!current = '\'') 
          && not (!current = _EOF) do
        assert(!current <> '\n');
        Buffer.add_char buffer !current;
        next_char()
      done;
      Buffer.add_char buffer !current;
      next_char();
      Message.print Message.Debug (lazy (Buffer.contents buffer));
      Buffer.contents buffer
  in

  (*return the chars until the next whitespace or the next control char
    takes at least one char*)
  let buffer_to_next_ws () =
    if !current = '\'' then
      buffer_to_next_little_thing_above ()
    else
      begin
        let buffer = Buffer.create 0 in
          Buffer.add_char buffer !current;
          next_char();
          while not (CharSet.mem !current whitespace) 
              && not (CharSet.mem !current ctrlChar)
              && not (!current = _EOF) do
            Buffer.add_char buffer !current;
            next_char()
          done;
          Buffer.contents buffer
      end
  in

  (*
  term :: individual_term
        | '(' term ')'
        | '+' '[' term_lst ']'
        | '*' number term
        | uninterpreted_function_symbol '[' term_lst ']'
        | # number term
        | @ number
  *)
  let rec term () =
    match !current with
    | '(' ->
      begin
        next_token();
        let f = term() in
          if !current = ')' then
            begin
              next_token();
              f
            end
          else
            failwith "foci parsing: syntax error (parenthesis mismatch)"
      end
    | '+' ->
      begin
        next_token();
        if !current <> _LBRACK then
          failwith "foci parsing: syntax error (missing '[')";
        next_token();
        let f_lst = term_lst() in
          if !current <> _RBRACK then
            failwith "foci parsing: syntax error (missing ']')";
          next_token();
          Sum f_lst
      end
    | '*' ->
      begin
        next_token();
        let n_str = buffer_to_next_ws () in
        let n = if String.contains n_str '/' then
            (*rationnal number*)
            let limit = String.index n_str '/' in
            let num = String.sub n_str 0 limit in
            let denom = String.sub n_str (limit + 1) ((String.length n_str) - limit -1) in
              (float_of_string num) /. (float_of_string denom)
          else
            float_of_string n_str
        in
          next_token2();
          Coeff ( n, term() )
      end
    |  _  -> (* uninterpreted fct sym or individual_term or cst *)
      begin
        let sym = buffer_to_next_ws () in
          next_token2();
          if !current <> _LBRACK then
            (*individual_term or cst*)
            try
              let n = if String.contains sym '/' then
                (*rationnal number*)
                let limit = String.index sym '/' in
                let num = String.sub sym 0 limit in
                let denom = String.sub sym (limit + 1) ((String.length sym) - limit -1) in
                  (float_of_string num) /. (float_of_string denom)
              else
                float_of_string sym
              in
                Constant (n)
            with _ ->
              Variable sym
          else
            (*uninterpreted_function_symbol*)
            begin
              next_token();
              let args = term_lst() in
                if !current <> _RBRACK then
                  failwith "foci parsing: syntax error (missing ']')";
                next_token();
                Application ( sym, args )
            end
      end
  (*
  term_lst :: term term_lst
            | empty
  *)
  and term_lst () =
    let rec iter acc =
      if !current <> _RBRACK then
        begin
          iter ( (term()) :: acc)
        end
      else
        List.rev acc
    in
      iter []
  in

  (*
  formula :: propositional_variable
           | '(' formula ')'
           | '=' term term
           | '<=' term term
           | '<' term term
           | '&' '[' formula_lst ']'
           | '|' '[' formula_lst ']'
           | '~' formula
           | 'true'
           | 'false'
  *)
  let rec formula () =
    match !current with
    | '(' ->
      begin
        next_token();
        let f = formula() in
          if !current = ')' then
            begin
              next_token();
              f
            end
          else
            failwith "foci parsing: syntax error (parenthesis mismatch)"
      end
    | '=' ->
      begin
        next_token();
        let t1 = term () in
        let t2 = term () in
          Eq (t1, t2)
      end
    | '<' ->
      begin
        next_char();
        if !current <> '=' then
          begin
            next_token2();
            let t1 = term () in
            let t2 = term () in
              Lt(t1,t2)
          end
        else
          begin
            next_token();
            let t1 = term () in
            let t2 = term () in
              Leq(t1,t2)
          end
      end
    | '&' ->
      begin
        next_token();
        if !current <> _LBRACK then
          failwith "foci parsing: syntax error (missing '[')";
        next_token();
        let f_lst = formula_lst () in
          if !current <> _RBRACK then
            failwith "foci parsing: syntax error (missing ']')";
          next_token();
          And f_lst
      end
    | '|' ->
      begin
        next_token();
        if !current <> _LBRACK then
          failwith "foci parsing: syntax error (missing '[')";
        next_token();
        let f_lst = formula_lst () in
          if !current <> _RBRACK then
            failwith "foci parsing: syntax error (missing ']')";
          next_token();
          Or f_lst
      end
    | '~' ->
      begin
        next_token();
        Not (formula ())
      end
    |  _  ->
      begin
        (*propositional_variable true or false*)
        let var = buffer_to_next_ws () in
          next_token2();
          match var with
          | "true" -> True
          | "false" -> False
          | _ -> Atom (int_of_string var)(*TODO hashtbl for numbering*)
      end
  
  (*
  formula_lst :: formula formula_lst
               | empty
  *)
  and formula_lst () =
    let rec iter acc =
      if !current <> _RBRACK then
        begin
          iter ( (formula()) :: acc)
        end
      else
        List.rev acc
    in
      iter []
  in

  (*
  file :: formula [; formula]
  *)
  let rec file () =
    let rec iter acc =
      let acc2 = (formula()) :: acc in
        if !current = _SEMICOLON then
          begin
            next_token();
            iter acc2
          end
        else
          acc2
  in
    iter []

  in
    next_token() ;
    List.rev (file())
