open Sat

let dpll_case name level cnf =
  let open Alcotest in
  test_case name level (fun () ->
      let expected =
        match Minisat_solver.solve cnf with UNSAT -> false | SAT _ -> true
      in
      let actual =
        match Dpll2.solve cnf with UNSAT -> false | SAT _ -> true
      in
      check bool name expected actual)

let cases =
  [
    dpll_case "SAT" `Quick
      [
        [ -1; -2 ];
        [ -1; 3 ];
        [ -3; -4 ];
        [ 2; 4; 5 ];
        [ -5; 6; -7 ];
        [ 2; 7; 8 ];
        [ -8; -9 ];
        [ -8; 10 ];
        [ 9; -10; 11 ];
        [ -10; -12 ];
        [ -11; 12 ];
      ];
  ]

let () =
  let open Alcotest in
  run "DPLL" [ ("DPLL", cases) ]
