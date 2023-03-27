(* fast DPLL implementation *)

module Clauses : sig
  type t
  type propagate_result = Sat | Conflict | Continue

  val create : int -> t
  val add_clause : t -> Lit.t array -> unit
  val propagate : t -> Assign.t -> Lit.t option -> propagate_result
end = struct
  (* w1 * w2 * literal array *)
  type clause = int * int * Lit.t array
  type watched_clauses = int list array
  type t = clause array ref * watched_clauses
  type propagate_result = Sat | Conflict | Continue

  type clause_type =
    | CSat of int
    | CConflict
    | CUnit of int
    | CMore of int * int

  let create nvars =
    let watched = Array.make (nvars + 1) [] in
    (ref [||], watched)

  let add_clause (clauses, watched_clauses) literals =
    let literals = Array.map Fun.id literals in
    Array.sort compare literals;
    let clause = (0, 0, literals) in
    let i = Array.length !clauses in
    clauses := Array.append !clauses [| clause |];
    watched_clauses.(0) <- i :: watched_clauses.(0)

  let clause_step (clauses, watched_clauses) assign i cause =
    let w1, w2, lits = !clauses.(i) in
    let update_clause w1 w2 =
      assert (w1 <> w2);
      let w1, w2 = if w1 < w2 then (w1, w2) else (w2, w1) in
      !clauses.(i) <- (w1, w2, lits)
    in
    let watch w =
      let v = Lit.var @@ lits.(w) in
      assert (v <> 0);
      watched_clauses.(v) <- i :: watched_clauses.(v)
    in
    let watch_unbound () = watched_clauses.(0) <- i :: watched_clauses.(0) in
    let check_type found_ua start =
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
          | Assign.False -> CSat j
          (* negative *)
          | Assign.True -> loop found (j + 1)
      in
      loop found_ua (start + 1)
    in
    if w1 = w2 then
      let uas, ty =
        let len = Array.length lits in
        let rec loop uas sat j =
          if j = len then (List.rev uas, sat)
          else
            match Assign.xor assign lits.(j) with
            (* unassigned *)
            | Assign.Unknown ->
                let uas = match uas with [] | [ _ ] -> j :: uas | _ -> uas in
                loop uas sat (j + 1)
            (* positive *)
            | Assign.False -> loop uas (Some j) (j + 1)
            (* negative *)
            | Assign.True -> loop uas sat (j + 1)
        in
        let uas, sat = loop [] None 0 in
        match (uas, sat) with
        | _, Some j -> (uas, CSat j)
        | [], None -> (uas, CConflict)
        | [ j ], None -> (uas, CUnit j)
        | j1 :: j2 :: _, None -> (uas, CMore (j1, j2))
      in
      let () =
        match (ty, uas) with
        (* TODO: watch currently assigned vars *)
        | CConflict, _ -> watch_unbound ()
        | CUnit _, _ -> watch_unbound ()
        | CSat _, [] -> watch_unbound ()
        | CSat w1, w2 :: _ ->
            watch w1;
            watch w2;
            update_clause w1 w2
        | CMore (w1, w2), _ ->
            watch w1;
            watch w2;
            update_clause w1 w2
      in
      ty
    else
      let wl1, wl2 = (lits.(w1), lits.(w2)) in
      let watch_with_cause () =
        if cause = Lit.var wl1 then watch w1
        else if cause = Lit.var wl2 then watch w2
        else ()
      in
      match (Assign.xor assign wl1, Assign.xor assign wl2) with
      | Assign.Unknown, Assign.Unknown ->
          watch_with_cause ();
          CMore (w1, w2)
      | Assign.False, _ ->
          watch_with_cause ();
          CSat w1
      | _, Assign.False ->
          watch_with_cause ();
          CSat w2
      (* w1: unassgined *)
      | Assign.Unknown, Assign.True -> (
          match check_type (Some w1) w2 with
          | CSat w as ty ->
              assert (w <> w1);
              (* w2 -> w *)
              watch w;
              update_clause w1 w;
              ty
          | CUnit w1' as ty ->
              assert (w1 = w1');
              watch w2;
              ty
          | CMore (w1', w2') as ty ->
              assert (w1 = w1' || w1 = w2');
              let w1, w2 = if w1 = w1' then (w1, w2') else (w1, w1') in
              watch w2;
              update_clause w1 w2;
              ty
          | CConflict -> failwith "w1: cannot conflict")
      (* w2: unassgined *)
      | Assign.True, Assign.Unknown -> (
          match check_type (Some w2) w2 with
          | CSat w as ty ->
              assert (w <> w2);
              (* w1 -> w *)
              watch w;
              update_clause w w2;
              ty
          | CUnit w2' as ty ->
              assert (w2 = w2');
              watch w1;
              ty
          | CMore (w1', w2') as ty ->
              assert (w2 = w1' || w2 = w2');
              let w1, w2 = if w2 = w2' then (w1', w2) else (w2', w2) in
              watch w1;
              update_clause w1 w2;
              ty
          | CConflict -> failwith "w2: cannot conflict")
      | Assign.True, Assign.True -> (
          match check_type None w2 with
          | (CSat _ | CConflict) as ty ->
              watch_with_cause ();
              ty
          | CUnit w as ty ->
              watch w;
              let w' = if cause = Lit.var wl1 then w2 else w1 in
              update_clause w w';
              ty
          | CMore (w1', w2') as ty ->
              watch w1';
              watch w2';
              update_clause w1' w2';
              ty)

  let propagate clauses assign decide =
    let clause_array, watched_clauses = clauses in
    decide |> Option.iter (fun l -> Assign.assign assign l);
    let vars = 0 :: Option.(decide |> map Lit.var |> to_list) in
    let rec loop vars =
      match vars with
      | [] -> Continue
      | v :: vars -> (
          let cls = watched_clauses.(v) in
          watched_clauses.(v) <- [];
          let rec aux vars cls =
            match cls with
            | [] -> (vars, true)
            | i :: cls -> (
                match clause_step clauses assign i v with
                | CSat _ | CMore _ -> aux vars cls
                | CConflict ->
                    watched_clauses.(v) <-
                      List.rev_append cls watched_clauses.(v);
                    (vars, false)
                | CUnit j ->
                    let _, _, lits = !clause_array.(i) in
                    let l = lits.(j) in
                    Assign.assign assign l;
                    let v' = Lit.var l in
                    aux (v' :: vars) cls)
          in
          match aux vars cls with
          | vars, true -> loop vars
          | _, false -> Conflict)
    in
    loop vars
end

let solve ?(debug = false) cnf =
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
    | None ->
        let assign = Assign.to_list assign in
        if Cnf.assign_is_valid cnf assign then Cnf.SAT assign else Cnf.UNSAT
    | Some v -> (
        let lit = Lit.make v in
        match propagate level lit with
        | Cnf.SAT _ as sat -> sat
        | Cnf.UNSAT ->
            let lit = Lit.neg lit in
            propagate level lit)
  and propagate level lit =
    Assign.set_level assign level;
    match Clauses.propagate clauses assign (Some lit) with
    | Clauses.Sat -> Cnf.SAT (Assign.to_list assign)
    | Clauses.Conflict -> Cnf.UNSAT
    | Clauses.Continue ->
        (if debug then
           cnf
           |> List.iteri @@ fun i lits ->
              let string_of_assign () =
                Assign.to_list assign |> List.map string_of_int
                |> String.concat ","
              in
              let string_of_lits () =
                lits |> List.map string_of_int |> String.concat ","
              in
              let rec check_type ua lits =
                match (lits, ua) with
                | [], Some l ->
                    (* unit clause *)
                    Printf.eprintf "unit: (%d; %s) -> %d\n assign:%s\n" i
                      (string_of_lits ()) l (string_of_assign ());

                    assert false
                | [], None ->
                    (* conflict clause *)
                    Printf.eprintf "conflict: (%d; %s)\n assign:%s\n" i
                      (string_of_lits ()) (string_of_assign ());
                    assert false
                | l :: lits, ua -> (
                    match (Assign.value assign (abs l), l > 0, ua) with
                    | Assign.Unknown, _, None -> check_type (Some l) lits
                    | Assign.Unknown, _, Some _ ->
                        (* multiple unassigned literals *) ()
                    | Assign.True, true, _ | Assign.False, false, _ ->
                        (* satisfied *) ()
                    | Assign.True, false, _ | Assign.False, true, _ ->
                        check_type ua lits)
              in
              check_type None lits);
        select (level + 1)
  in
  select 1
