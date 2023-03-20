let success_case name src expected =
  Alcotest.test_case name `Quick (fun () ->
      let result = Dimacs.parse (Lexing.from_string src) |> Result.get_ok in
      Alcotest.(check (list (list int))) name expected result)

let parse_cases =
  [
    success_case "simple" "p cnf 3 2\n 1 2 3 0\n 1 -2 3 0\n"
      [ [ 1; 2; 3 ]; [ 1; -2; 3 ] ];
    success_case "comment"
      "c comment\nc p cnf 3 2\np cnf 3 2\n 1 2 3 0\n 1 -2 3 0\n"
      [ [ 1; 2; 3 ]; [ 1; -2; 3 ] ];
  ]

let () =
  let open Alcotest in
  run "DIMACS" [ ("Parse", parse_cases) ]
