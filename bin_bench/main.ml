open Eio

let solve_with_measure ~mono_clock solver cnf () =
  let before = Time.Mono.now mono_clock in
  let result = solver cnf in
  let after = Time.Mono.now mono_clock in
  Result.ok (result, Mtime.span before after)

let timeout = 10.0
let solver cnf = Sat.Solver.dpll_solve ~watched_literal:false cnf

let main ~clock ~mono_clock ~cwd =
  let benchmark_dir = Path.(cwd / "bench_cases") in
  let files = Path.read_dir benchmark_dir in
  files
  |> ((0, 0, Mtime.Span.zero)
     |> List.fold_left @@ fun state filename ->
        Format.printf "Solving %s@." filename;
        let path = Path.(benchmark_dir / filename) in
        let content = Path.load path in
        match Dimacs.parse (Lexing.from_string content) with
        | Result.Error (pos, mes) ->
            let col = pos.pos_cnum - pos.pos_bol in
            Printf.printf "%d:%d syntax error: %s\n" pos.pos_lnum col mes;
            state
        | Result.Ok cnf -> (
            let task = solve_with_measure ~mono_clock solver cnf in
            match Time.with_timeout clock timeout task with
            | Result.Ok (result, time_span) ->
                let result =
                  match result with
                  | Sat.Cnf.SAT _ -> "SAT"
                  | Sat.Cnf.UNSAT -> "UNSAT"
                in
                Format.printf " %s (%a)@." result Mtime.Span.pp time_span;
                let count, solved, span = state in
                (count + 1, solved + 1, Mtime.Span.add span time_span)
            | Result.Error `Timeout ->
                Printf.printf " Timeout@.";
                let count, solved, span = state in
                (count + 1, solved, span)))
  |> fun (count, solved, span) ->
  let solved_percent = float_of_int solved /. float_of_int count *. 100.0 in
  let span_per_problem =
    let ns = Mtime.Span.to_uint64_ns span in
    let ns_per_problem = Int64.div ns (Int64.of_int count) in
    Mtime.Span.of_uint64_ns ns_per_problem
  in
  Format.printf "Solved %d/%d (%.2f%%) in %a per problem@." solved count
    solved_percent Mtime.Span.pp span_per_problem

let () =
  Eio_main.run @@ fun env ->
  Eio.Stdenv.(
    main ~clock:(clock env) ~mono_clock:(mono_clock env) ~cwd:(cwd env))
