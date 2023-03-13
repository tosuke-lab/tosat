type clause = int list (* literal: x_i -> i, ¬x_i -> -i *)
type cnf = clause list

let string_of_clause clause =
    let inner = List.map string_of_int clause |> String.concat " " in
    "{" ^ inner ^ "}"
let string_of_cnf cnf = List.map string_of_clause cnf |> String.concat ", "

type result = SAT of int list | UNSAT

module LitSet = Set.Make (struct
    type t = int
    let compare = compare
end)

let rec unassigned_var = function
    | [] -> failwith "clauses are all satisfied"
    | []::clauses -> unassigned_var clauses
    | (lit::_)::_ -> abs lit
let dpll clauses =
    let rec solve clauses =
        match clauses with
        | [] -> SAT []
        | _ -> begin
            print_string (string_of_cnf clauses); print_newline ();
            let unit_clause = clauses |> List.find_opt (function [_] -> true | _ -> false) in
            match unit_clause with
            | Some [lit] -> begin
                match propagate [] lit clauses with
                | SAT model -> SAT (lit::model)
                | UNSAT -> UNSAT
            end
            | _ -> begin
                let var = unassigned_var clauses in
                match propagate [] var clauses with
                | SAT model -> SAT (var::model)
                | UNSAT -> begin
                    match propagate [] (-var) clauses with
                    | SAT model -> SAT (-var::model)
                    | UNSAT -> UNSAT
                end
            end
        end
    and propagate acc lit clauses =
        let rec propagate_clause acc lit clause =
            match clause with
            | [] -> acc
            | l::_ when l = lit -> []
            | l::clause when l = -lit -> propagate_clause acc lit clause
            | l::clause -> propagate_clause (l::acc) lit clause
        in
        match clauses with
        | [] -> solve acc
        | [l]::_ when l = -lit -> UNSAT
        | clause::clauses ->
            let clause' = propagate_clause [] lit clause in
            match clause' with
            | [] -> propagate acc lit clauses
            | _ -> propagate (clause'::acc) lit clauses
    in
    solve clauses
            
