let minisat_solver = Sat.Minisat_solver.solve
let dpll_solver = Sat.Dpll.solve
let dpll2_solver = Sat.Dpll2.solve ~debug:false ~watched_literal:true

type backend = MINISAT | DPLL | DPLL2 | DPLL2minusWL

let parse_backend = function
  | "minisat" -> MINISAT
  | "dpll" -> DPLL
  | "dpll2" -> DPLL2
  | "dpll2-wl" -> DPLL2minusWL
  | _ -> failwith "unknown backend"

let solver = function
  | MINISAT -> minisat_solver
  | DPLL -> dpll_solver
  | DPLL2 -> dpll2_solver
  | DPLL2minusWL -> Sat.Dpll2.solve ~debug:false ~watched_literal:false

let print_result = function
  | Sat.Cnf.SAT assign ->
      print_endline "SAT";
      assign |> List.iter (fun v -> Printf.printf "%d " v);
      print_endline "0"
  | Sat.Cnf.UNSAT -> print_endline "UNSAT"

let () =
  let backend = parse_backend Sys.argv.(1) in
  let result = Dimacs.parse (Lexing.from_channel stdin) in
  match result with
  | Result.Error (pos, mes) ->
      let col = pos.pos_cnum - pos.pos_bol in
      Printf.fprintf stderr "%s:%d:%d syntax error: %s" pos.pos_fname
        pos.pos_lnum col mes
  | Result.Ok clauses ->
      let result = solver backend clauses in
      print_result result
