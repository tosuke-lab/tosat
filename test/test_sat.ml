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

let simple_cases solve =
  let sat_case = sat_case solve in
  [
    sat_case "simple-SAT" `Quick
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

let find_project_dir () =
  let cwd = Sys.getcwd () |> Fpath.v in
  let rec loop dir =
    let project = Fpath.(dir / "dune-project") in
    if Sys.file_exists (Fpath.to_string project) then dir
    else loop @@ Fpath.parent dir
  in
  loop cwd

let ( let@ ) x k = x k

let[@warning "-32"] file_cases =
  let project_dir = find_project_dir () in
  let cases_dir = Fpath.(project_dir / "test" / "test_cases") in
  let cases =
    Sys.readdir (Fpath.to_string cases_dir)
    |> Array.to_seq
    |> Seq.map (fun f -> Fpath.(cases_dir / f))
    |> Seq.filter (Fpath.has_ext "cnf")
    |> Seq.map (fun p ->
           let name = p |> Fpath.rem_ext |> Fpath.basename in
           let@ chan = In_channel.with_open_text (Fpath.to_string p) in
           let lex = Lexing.from_channel chan in
           let cnf = Dimacs.parse lex in
           match cnf with
           | Error _ ->
               let msg = Printf.sprintf "%s: parse error" name in
               Alcotest.fail msg
           | Ok cnf -> (name, cnf))
    |> List.of_seq
  in
  fun solve ->
    cases |> List.map (fun (name, cnf) -> sat_case solve name `Slow cnf)

let dpll_test = ("DPLL", simple_cases Dpll.solve)

let dpll2_test =
  let solve = Solver.dpll_solve ~debug:true in
  let file_cases = file_cases solve in
  ("DPLL2", simple_cases solve @ file_cases)

let cdcl_test =
  let solve = Solver.cdcl_solve ~debug:true in
  let file_cases = file_cases solve in
  ("CDCL", simple_cases solve @ file_cases)

let () =
  let open Alcotest in
  run "Sat" [ dpll_test; dpll2_test; cdcl_test ]
