(* fast DPLL implementation *)

module Clauses : sig
  type t
  type propagate_result = Sat | Conflict | Continue

  val create : int -> t
  val add_clause : t -> Lit.t array -> unit
  val propagate : t -> Assign.t -> Lit.t option -> propagate_result
  val full_propagate : t -> Assign.t -> propagate_result
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

  let watch_clause (_, watched_clauses) v i =
    watched_clauses.(v) <- i :: watched_clauses.(v)

  let add_clause clauses literals =
    let clause_array, _ = clauses in
    let literals = Array.map Fun.id literals in
    Array.sort compare literals;
    let clause = (0, 0, literals) in
    let i = Array.length !clause_array in
    clause_array := Array.append !clause_array [| clause |];
    watch_clause clauses 0 i

  let clause_step clauses assign i cause_var =
    let clauses_array, _ = clauses in
    let w1, w2, lits = !clauses_array.(i) in
    assert ((w2 = 0 && w1 = w2) || w1 < w2);
    let update_watched_literals w1' w2' =
      assert (w1' <> w2');
      let w1', w2' = if w1' < w2' then (w1', w2') else (w2', w1') in
      let first_update = w1 = w2 in
      if (w1 = w1' || w1 = w2') && cause_var = Lit.var @@ lits.(w1) then
        watch_clause clauses cause_var i;
      if (w2 = w1' || w2 = w2') && cause_var = Lit.var @@ lits.(w2) then
        watch_clause clauses cause_var i;
      if first_update || (w1' <> w1 && w1' <> w2) then
        watch_clause clauses (Lit.var @@ lits.(w1')) i;
      if first_update || (w2' <> w1 && w2' <> w2) then
        watch_clause clauses (Lit.var @@ lits.(w2')) i;
      !clauses_array.(i) <- (w1', w2', lits)
    in
    let watch_unbound () = watch_clause clauses 0 i in

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
        | CSat w1', w2' :: _ -> update_watched_literals w1' w2'
        | CMore (w1', w2'), _ -> update_watched_literals w1' w2'
      in
      ty
    else
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
      let wl1, wl2 = (lits.(w1), lits.(w2)) in
      let w1', w2', ty =
        let comp1, comp2 = (Assign.xor assign wl1, Assign.xor assign wl2) in
        match (comp1, comp2) with
        | Assign.Unknown, Assign.Unknown -> (w1, w2, CMore (w1, w2))
        | Assign.False, _ -> (w1, w2, CSat w1)
        | _, Assign.False -> (w1, w2, CSat w2)
        (* w1: unassgined *)
        | Assign.Unknown, Assign.True -> (
            match check_type (Some w1) w2 with
            | CSat w2' as ty ->
                assert (w2' <> w1);
                (w1, w2', ty)
            | CUnit w1' as ty ->
                assert (w1 = w1');
                (w1, w2, ty)
            | CMore (w1', w2') as ty ->
                assert (w1 = w1' || w1 = w2');
                (w1', w2', ty)
            | CConflict -> failwith "w1: cannot conflict")
        (* w2: unassgined *)
        | Assign.True, Assign.Unknown -> (
            match check_type (Some w2) w2 with
            | CSat w1' as ty ->
                assert (w1' <> w2);
                (w1', w2, ty)
            | CUnit w2' as ty ->
                assert (w2 = w2');
                (w1, w2, ty)
            | CMore (w1', w2') as ty ->
                assert (w2 = w1' || w2 = w2');
                (w1', w2', ty)
            | CConflict -> failwith "w2: cannot conflict")
        | Assign.True, Assign.True -> (
            match check_type None w2 with
            | (CSat _ | CConflict) as ty -> (w1, w2, ty)
            | CUnit w as ty ->
                let w' = if cause_var = Lit.var wl1 then w2 else w1 in
                (w, w', ty)
            | CMore (w1', w2') as ty -> (w1', w2', ty))
      in
      update_watched_literals w1' w2';
      ty

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

  let rec full_propagate clauses assign =
    let clause_array, _ = clauses in
    let check_type i =
      let _, _, lits = !clause_array.(i) in
      let len = Array.length lits in
      let rec loop ua j =
        if j = len then match ua with None -> CConflict | Some j -> CUnit j
        else
          match (Assign.xor assign lits.(j), ua) with
          | Assign.Unknown, None -> loop (Some j) (j + 1)
          | Assign.Unknown, Some j' -> CMore (j, j')
          | Assign.True, _ -> loop ua (j + 1)
          | Assign.False, _ -> CSat j
      in
      loop None 0
    in
    let nclauses = Array.length !clause_array in
    let rec loop has_ua new_assign i =
      if i = nclauses then
        match (has_ua, new_assign) with
        | true, true -> full_propagate clauses assign
        | true, false -> Continue
        | false, _ -> Sat
      else
        match check_type i with
        | CConflict -> Conflict
        | CSat _ -> loop has_ua new_assign (i + 1)
        | CMore _ -> loop true new_assign (i + 1)
        | CUnit j ->
            let _, _, lits = !clause_array.(i) in
            Assign.assign assign lits.(j);
            loop has_ua true (i + 1)
    in
    loop false false 0
end

let solve ?(debug = false) ?(watched_literal = true) cnf =
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
    let result =
      if watched_literal then Clauses.propagate clauses assign (Some lit)
      else (
        Assign.assign assign lit;
        Clauses.full_propagate clauses assign)
    in
    match result with
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
