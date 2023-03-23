open Sat

let sat_case solve name level cnf =
  let string_of_result = function Cnf.UNSAT -> "UNSAT" | Cnf.SAT _ -> "SAT" in
  Alcotest.test_case name level (fun () ->
      let result = solve cnf in
      let () =
        let name = name ^ ": check result type" in
        let expected = string_of_result @@ Minisat_solver.solve cnf in
        let actual = string_of_result @@ result in
        Alcotest.(check string) name expected actual
      in
      match result with
      | Cnf.UNSAT -> ()
      | Cnf.SAT assign ->
          let name = name ^ ": check satisfiability" in
          let expected = true in
          let actual = Cnf.assign_is_valid cnf assign in
          Alcotest.(check bool) name expected actual)

let cases solve =
  let sat_case = sat_case solve in
  [
    sat_case "SAT" `Quick
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
  run "Sat" [ ("DPLL", cases Dpll.solve); ("DPLL2", cases Dpll2.solve) ]
