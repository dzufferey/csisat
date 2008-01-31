
let main =
  Camlpico.init ();
  Camlpico.enable_trace ();
  Camlpico.adjust 3 ;
  Camlpico.add 3 ;
  Camlpico.add 0 ;
  Camlpico.add 1 ;
  Camlpico.add 0 ;
  Camlpico.add 2 ;
  Camlpico.add 0 ;
  Camlpico.add (-1) ;
  Camlpico.add (-2) ;
  Camlpico.add 0 ;
  let result = Camlpico.sat (-1) in
    if result = Camlpico.satisfiable() then print_endline "sat"
    else if result = Camlpico.unsatisfiable() then print_endline "unsat"
    else if result = Camlpico.unknown() then print_endline "unk";
    print_endline (string_of_int (Camlpico.corelit 1));
    print_endline (string_of_int (Camlpico.corelit 2));
    print_endline (string_of_int (Camlpico.corelit 3))

