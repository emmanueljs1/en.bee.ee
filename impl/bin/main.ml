open Impl.Stlc

let () =
  let _ : exp = App (Abs (Var 0), One) in
  print_endline "test"
