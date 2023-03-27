(* fast DPLL implementation *)

module Clauses : sig
  type t
  type propagate_result = Sat | Conflict | Continue

  val create : int -> t
  val add_clause : t -> Lit.t array -> unit
  val propagate : t -> Assign.t -> propagate_result
end = struct
  (* w1 * w2 * literal array *)
  type clause = int * int * Lit.t array
  type t = clause array ref
  type propagate_result = Sat | Conflict | Continue
  type clause_type = CSat | CConflict | CUnit of int | CMore of int * int

  let create _ = ref [||]

  let add_clause clauses literals =
    let literals = Array.map Fun.id literals in
    Array.sort compare literals;
    let clause = (0, 0, literals) in
    clauses := Array.append !clauses [| clause |]

  let propagate clauses assign =
    let clause_step i =
      let w1, w2, lits = !clauses.(i) in
      let update_clause w1 w2 =
        let w1, w2 = if w1 < w2 then (w1, w2) else (w2, w1) in
        !clauses.(i) <- (w1, w2, lits)
      in
      let watch _ = () in
      let watch_unbound () = () in
      let find_ua found start =
        let len = Array.length lits in
        let rec loop found j =
          if j = start then
            match found with Some j -> CUnit j | None -> CConflict
          else if j = len then loop found 0
          else
            match Assign.xor assign lits.(j) with
            (* unassigned *)
            | Assign.Unknown -> (
                match found with
                | Some j' when j = j' -> loop found (j + 1)
                | Some k -> CMore (j, k)
                | None -> loop (Some j) (j + 1))
            (* positive *)
            | Assign.False -> CSat
            (* negative *)
            | Assign.True -> loop found (j + 1)
        in
        loop found (start + 1)
      in
      if w1 = w2 then
        let ty =
          match Assign.xor assign lits.(w1) with
          | Assign.Unknown -> find_ua (Some w1) w1
          | Assign.False -> CSat
          | Assign.True -> find_ua None w1
        in
        let () =
          match ty with
          | CSat | CConflict | CUnit _ -> watch_unbound ()
          | CMore (w1', w2') ->
              watch w1';
              watch w2';
              update_clause w1' w2'
        in
        ty
      else
        let wl1, wl2 = (lits.(w1), lits.(w2)) in
        match (Assign.xor assign wl1, Assign.xor assign wl2) with
        | Assign.Unknown, Assign.Unknown ->
            watch w1;
            watch w2;
            CMore (w1, w2)
        | Assign.False, _ | _, Assign.False ->
            watch w1;
            watch w2;
            CSat
        (* w1: unassgined *)
        | Assign.Unknown, Assign.True -> (
            match find_ua (Some w1) w2 with
            | CSat ->
                watch w1;
                watch w2;
                CSat
            | CUnit w1' as ty ->
                assert (w1 = w1');
                watch w1;
                watch w2;
                ty
            | CMore (w1', w2') as ty ->
                assert (w1 = w1' || w1 = w2');
                watch w1;
                let w2 = if w2' = w2 then w1' else w2' in
                watch w2;
                update_clause w1 w2;
                ty
            | _ -> failwith "invalid")
        (* w2: unassgined *)
        | Assign.True, Assign.Unknown -> (
            match find_ua (Some w2) w2 with
            | CSat ->
                watch w1;
                watch w2;
                CSat
            | CUnit w2' as ty ->
                assert (w2 = w2');
                watch w1;
                watch w2;
                ty
            | CMore (w1', w2') as ty ->
                assert (w2 = w1' || w2 = w2');
                watch w2;
                let w1 = if w1' = w1 then w2' else w1' in
                watch w1;
                update_clause w1 w2;
                ty
            | _ -> failwith "invalid")
        | Assign.True, Assign.True -> (
            match find_ua None w2 with
            | (CSat | CConflict) as ty ->
                watch w1;
                watch w2;
                ty
            | CUnit w as ty ->
                watch w;
                watch w1;
                update_clause w w1;
                ty
            | CMore (w1', w2') as ty ->
                watch w1';
                watch w2';
                update_clause w1' w2';
                ty)
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
        | CMore _ -> aux true new_assign (i + 1)
        | CConflict -> Conflict
        | CUnit j ->
            let _, _, clause_lits = !clauses.(i) in
            let l = clause_lits.(j) in
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
    let cl = Clauses.create nvars in
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
