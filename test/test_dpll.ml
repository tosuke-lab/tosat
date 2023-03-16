let dpll_case name level cnf expected =
    let open Alcotest in
    test_case name level (fun () ->
        let actual =
            match Tosat.Solver.dpll cnf with
            | UNSAT -> false
            | SAT _ -> true
        in
        check bool name expected actual
    )

let cases = [
    dpll_case "SAT" `Quick
        ([[-1; -2]; [-1; 3]; [-3; -4]; [2; 4; 5]; [-5; 6; -7]; [2; 7; 8];
         [-8; -9]; [-8; 10]; [9; -10; 11]; [-10; -12]; [-11; 12]])
        true
]

let () =
    let open Alcotest in
    run "DPLL" [
        ("DPLL", cases)
    ]