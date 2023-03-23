open Cnf

module LitSet = Set.Make (struct
  type t = int

  let compare = compare
end)

let rec unassigned_var = function
  | [] -> failwith "clauses are all satisfied"
  | [] :: clauses -> unassigned_var clauses
  | (lit :: _) :: _ -> abs lit

let rec solve clauses =
  match clauses with
  | [] -> SAT []
  | _ -> (
      let unit_clause =
        clauses |> List.find_opt (function [ _ ] -> true | _ -> false)
      in
      match unit_clause with
      | Some [ lit ] -> (
          match propagate [] lit clauses with
          | SAT model -> SAT (lit :: model)
          | UNSAT -> UNSAT)
      | _ -> (
          let var = unassigned_var clauses in
          match propagate [] var clauses with
          | SAT model -> SAT (var :: model)
          | UNSAT -> (
              match propagate [] (-var) clauses with
              | SAT model -> SAT (-var :: model)
              | UNSAT -> UNSAT)))

and propagate acc lit clauses =
  let rec propagate_clause acc lit clause =
    match clause with
    | [] -> acc
    | l :: _ when l = lit -> []
    | l :: clause when l = -lit -> propagate_clause acc lit clause
    | l :: clause -> propagate_clause (l :: acc) lit clause
  in
  match clauses with
  | [] -> solve acc
  | [ l ] :: _ when l = -lit -> UNSAT
  | clause :: clauses -> (
      let clause' = propagate_clause [] lit clause in
      match clause' with
      | [] -> propagate acc lit clauses
      | _ -> propagate (clause' :: acc) lit clauses)
