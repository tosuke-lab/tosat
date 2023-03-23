open Minisat

let solve clauses =
  let nvars =
    clauses
    |> List.fold_left
         (fun m clause -> clause |> List.fold_left (fun m n -> max m (abs n)) m)
         0
  in
  let solver = Minisat.create () in
  let () =
    clauses
    |> List.iter (fun clause ->
           let clause =
             clause
             |> List.map (fun n ->
                    Lit.(if n > 0 then n |> make else -n |> make |> neg))
           in
           Minisat.add_clause_l solver clause)
  in
  try
    let () = Minisat.solve solver in
    let assign =
      Array.make nvars 0
      |> Array.mapi (fun i _ -> Lit.make (i + 1))
      |> Array.to_list
      |> List.filter_map (fun lit ->
             match Minisat.value solver lit with
             | Minisat.V_true -> Some (Lit.to_int lit)
             | Minisat.V_false -> Some (-Lit.to_int lit)
             | Minisat.V_undef -> None)
    in
    Cnf.SAT assign
  with Minisat.Unsat -> Cnf.UNSAT
