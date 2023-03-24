(* fast DPLL implementation *)

module Clauses : sig
  type t
  type propagate_result = Sat | Conflict | Continue

  val create : unit -> t
  val add_clause : t -> Lit.t array -> unit
  val propagate : t -> Assign.t -> propagate_result
end = struct
  type clause = Lit.t array
  type t = clause array ref
  type propagate_result = Sat | Conflict | Continue
  type clause_type = CSat | CUnit of Lit.t | CMore | CConflict

  let create () = ref [||]
  let add_clause clauses clause = clauses := Array.append !clauses [| clause |]

  let propagate clauses assign =
    let clause_step i =
      let clause = !clauses.(i) in
      let len = Array.length clause in
      let rec loop count unassigned j =
        if j = len then
          match count with 0 -> CConflict | 1 -> CUnit unassigned | _ -> CMore
        else
          let l = clause.(j) in
          match Assign.xor assign l with
          (* unassigned *)
          | Assign.Unknown -> loop (count + 1) l (j + 1)
          (* negated *)
          | Assign.True -> loop count unassigned (j + 1)
          (* satisfied *)
          | Assign.False -> CSat
      in
      loop 0 Lit.nil 0
    in
    let len = Array.length !clauses in
    let rec aux has_na new_assign i =
      if i = len then
        match (has_na, new_assign) with
        | true, true -> aux false false 0
        | true, false -> Continue
        | false, _ -> Sat
      else
        match clause_step i with
        | CSat -> aux has_na new_assign (i + 1)
        | CMore -> aux true new_assign (i + 1)
        | CConflict -> Conflict
        | CUnit l ->
            Assign.assign assign l;
            aux has_na true (i + 1)
    in
    aux false false 0
end

let solve cnf =
  let nvars =
    List.fold_left
      (fun acc c ->
        max acc (List.fold_left (fun acc lit -> max acc (abs lit)) 0 c))
      0 cnf
  in
  let clauses =
    let cl = Clauses.create () in
    List.iter
      (fun c ->
        let clause = Array.of_list (List.map Lit.make c) in
        Clauses.add_clause cl clause)
      cnf;
    cl
  in
  let assign = Assign.create nvars in
  let score = Fun.const 0 in
  let rec select level =
    match Assign.unassigned assign score with
    | None -> Cnf.UNSAT
    | Some v -> (
        let lit = Lit.make v in
        match propagate level lit with
        | Cnf.SAT _ as sat -> sat
        | Cnf.UNSAT ->
            let lit = Lit.neg lit in
            propagate level lit)
  and propagate level lit =
    Assign.set_level assign level;
    Assign.assign assign lit;
    match Clauses.propagate clauses assign with
    | Clauses.Sat -> Cnf.SAT (Assign.to_list assign)
    | Clauses.Conflict -> Cnf.UNSAT
    | Clauses.Continue -> select (level + 1)
  in
  select 1
