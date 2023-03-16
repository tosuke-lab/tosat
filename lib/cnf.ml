type clause = Clause of int list
type cnf = clause list
type result = SAT of int list | UNSAT

let from_list l = List.map (fun x -> Clause x) l

let string_of_clause (Clause lits) =
    let inner = List.map string_of_int lits |> String.concat " " in
    "{" ^ inner ^ "}"
let string_of_cnf cnf = List.map string_of_clause cnf |> String.concat ", "
