type t = int list list
type result = SAT of int list | UNSAT

let string_of_clause lits =
  let inner = List.map string_of_int lits |> String.concat " " in
  "{" ^ inner ^ "}"

let string_of_cnf cnf = List.map string_of_clause cnf |> String.concat ", "

module IntSet = Set.Make (struct
  type t = int

  let compare = compare
end)

let assign_is_valid cnf assign =
  let assign = IntSet.of_list assign in
  cnf |> List.for_all (List.exists (fun lit -> IntSet.mem lit assign))
