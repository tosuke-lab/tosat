(* fast DPLL/CDCL implementation *)

module Clauses : sig
  type t

  type trail =
    | TDecide of Lit.t
    | TImply of Lit.t * Lit.t array
    | TConflict of Lit.t array

  type propagate_result =
    | Sat
    | Conflict of trail list
    | Continue of trail list

  val create : int -> t
  val add_clause : t -> Lit.t array -> unit

  val propagate :
    ?debug:bool -> t -> Assign.t -> Lit.t option -> propagate_result

  val full_propagate :
    ?debug:bool -> t -> Assign.t -> Lit.t option -> propagate_result

  val print_trail : trail list -> unit [@@warning "-32"]
end = struct
  (* w1 * w2 * literal array *)
  type clause = int * int * Lit.t array
  type watched_clauses = int list array

  type t = {
    mutable clause_array : clause array;
    watched_clauses : watched_clauses;
  }

  type trail =
    | TDecide of Lit.t
    | TImply of Lit.t * Lit.t array
    | TConflict of Lit.t array

  type propagate_result =
    | Sat
    | Conflict of trail list
    | Continue of trail list

  type clause_type =
    | CSat of int
    | CConflict
    | CUnit of int
    | CMore of int * int

  let print_trail (trail : trail list) : unit =
    let rec aux trail =
      match trail with
      | [] -> ()
      | TDecide l :: trail ->
          Printf.eprintf "decide: %d\n" (Lit.to_int l);
          aux trail
      | TImply (l, lits) :: trail ->
          Printf.eprintf " imply: (%s) -> %d\n"
            (lits |> Array.to_list
            |> List.map (fun l -> l |> Lit.to_int |> string_of_int)
            |> String.concat ",")
            (Lit.to_int l);
          aux trail
      | TConflict lits :: trail ->
          Printf.eprintf " conflict: (%s)\n"
            (lits |> Array.to_list
            |> List.map (fun l -> l |> Lit.to_int |> string_of_int)
            |> String.concat ", ");
          aux trail
    in
    aux (List.rev trail)

  let create (nvars : int) : t =
    let clause_array = [||] in
    let watched_clauses = Array.make (nvars + 1) [] in
    { clause_array; watched_clauses }

  let watch_clause (clauses : t) (var : int) (clause_index : int) : unit =
    let wcs = clauses.watched_clauses in
    wcs.(var) <- clause_index :: wcs.(var)

  let add_clause (clauses : t) (literals : Lit.t array) : unit =
    let literals = Array.map Fun.id literals in
    Array.sort compare literals;
    let clause = (0, 0, literals) in
    let ca = clauses.clause_array in
    let i = Array.length ca in
    clauses.clause_array <- Array.append ca [| clause |];
    watch_clause clauses 0 i

  let clause_step (clauses : t) (assign : Assign.t) (clause_index : int)
      (cause_var : int) : clause_type =
    let ci = clause_index in
    let ca = clauses.clause_array in
    let w1, w2, lits = ca.(ci) in
    assert ((w2 = 0 && w1 = w2) || w1 < w2);
    let update_watched_literals w1' w2' =
      assert (w1' <> w2');
      let w1', w2' = if w1' < w2' then (w1', w2') else (w2', w1') in
      let first_update = w1 = w2 in
      if (w1 = w1' || w1 = w2') && cause_var = Lit.var @@ lits.(w1) then
        watch_clause clauses cause_var ci;
      if (w2 = w1' || w2 = w2') && cause_var = Lit.var @@ lits.(w2) then
        watch_clause clauses cause_var ci;
      if first_update || (w1' <> w1 && w1' <> w2) then
        watch_clause clauses (Lit.var @@ lits.(w1')) ci;
      if first_update || (w2' <> w1 && w2' <> w2) then
        watch_clause clauses (Lit.var @@ lits.(w2')) ci;
      ca.(ci) <- (w1', w2', lits)
    in
    let watch_unbound () = watch_clause clauses 0 ci in

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

  let assert_continue (clauses : t) (assign : Assign.t) (trail : trail list) :
      unit =
    let string_of_assign =
      lazy (Assign.to_list assign |> List.map string_of_int |> String.concat ",")
    in
    clauses.clause_array
    |> Array.iter (fun (_, _, lits) ->
           let string_of_lits =
             lazy
               (lits |> Array.to_list
               |> List.map (fun l -> l |> Lit.to_int |> string_of_int)
               |> String.concat ",")
           in
           let rec check_type ua i =
             if i = Array.length lits then (
               match ua with
               | Some l ->
                   (* unit clause *)
                   print_trail trail;
                   Printf.eprintf "unit clause: (%s) -> %d\n assign: %s\n"
                     (Lazy.force string_of_lits)
                     (Lit.to_int l)
                     (Lazy.force string_of_assign);
                   assert false
               | None ->
                   (* conflict clause *)
                   print_trail trail;
                   Printf.eprintf "conflict clause: (%s)\n assign: %s\n"
                     (Lazy.force string_of_lits)
                     (Lazy.force string_of_assign);
                   assert false)
             else
               let l = lits.(i) in
               match (Assign.xor assign l, ua) with
               | Assign.Unknown, None -> check_type (Some l) (i + 1)
               | Assign.Unknown, Some _ -> (* CMore *) ()
               | Assign.True, _ -> check_type ua (i + 1)
               | Assign.False, _ -> (* CSat *) ()
           in
           check_type None 0)

  let propagate ?(debug = false) (clauses : t) (assign : Assign.t)
      (decision : Lit.t option) : propagate_result =
    decision |> Option.iter (fun l -> Assign.assign assign l);
    let trail = Option.(decision |> map (fun l -> TDecide l) |> to_list) in
    let vars = 0 :: Option.(decision |> map Lit.var |> to_list) in
    let rec loop_vars trail vars =
      match vars with
      | [] ->
          if debug then assert_continue clauses assign trail;
          Continue trail
      | v :: vars ->
          let wcs = clauses.watched_clauses in
          let cs = wcs.(v) in
          wcs.(v) <- [];
          loop_cs trail v vars cs
    and loop_cs trail v vars cs =
      let wcs = clauses.watched_clauses in
      match cs with
      | [] -> loop_vars trail vars
      | i :: cs -> (
          match clause_step clauses assign i v with
          | CSat _ | CMore _ -> loop_cs trail v vars cs
          | CConflict ->
              let _, _, lits = clauses.clause_array.(i) in
              let trail = TConflict lits :: trail in
              wcs.(v) <- List.rev_append cs wcs.(v);
              Conflict trail
          | CUnit j ->
              let _, _, lits = clauses.clause_array.(i) in
              let l = lits.(j) in
              let trail = TImply (l, lits) :: trail in
              Assign.assign assign l;
              let v' = Lit.var l in
              loop_cs trail v (v' :: vars) cs)
    in
    loop_vars trail vars

  let rec full_propagate ?(debug = false) (clauses : t) (assign : Assign.t)
      (decision : Lit.t option) : propagate_result =
    let ca = clauses.clause_array in
    decision |> Option.iter (Assign.assign assign);
    let trail = Option.(decision |> map (fun l -> TDecide l) |> to_list) in
    let check_type i =
      let _, _, lits = ca.(i) in
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
    let nclauses = Array.length ca in
    let rec loop trail has_ua new_assign i =
      if i = nclauses then
        match (has_ua, new_assign) with
        | true, true -> full_propagate clauses assign None
        | true, false ->
            if debug then assert_continue clauses assign trail;
            Continue trail
        | false, _ -> Sat
      else
        match check_type i with
        | CConflict ->
            let _, _, lits = ca.(i) in
            let trail = TConflict lits :: trail in
            Conflict trail
        | CSat _ -> loop trail has_ua new_assign (i + 1)
        | CMore _ -> loop trail true new_assign (i + 1)
        | CUnit j ->
            let _, _, lits = ca.(i) in
            let l = lits.(j) in
            Assign.assign assign l;
            let trail = TImply (l, lits) :: trail in
            loop trail has_ua true (i + 1)
    in
    loop trail false false 0
end

let first_uip_cut (assign : Assign.t)
    (trail : Clauses.trail list) : int * Lit.t array =
  let module S = Set.Make (struct
    type t = int

    let compare = compare
  end) in
  match trail with
  | Clauses.TConflict conflict_clause :: _ as trail ->
      let dlevel =
        conflict_clause
        |> Array.fold_left
             (fun acc l -> max acc (Assign.level assign @@ Lit.var l))
             0
      in
      (* cut = S.union ocut icut *)
      let ocut, icut = (S.empty, S.empty) in
      let rec aux ocut icut trail =
        match trail with
        | [] -> failwith "first_uip_cut: no UIP found"
        | Clauses.TConflict lits :: trail -> (
            let ocut, icut =
              lits
              |> ((ocut, icut)
                 |> Array.fold_left (fun (ocut, icut) l ->
                        let v = Lit.var l in
                        let level = Assign.level assign v in
                        if level = dlevel then (ocut, icut |> S.add v)
                        else (ocut |> S.add v, icut)))
            in
            match S.cardinal icut with
            | 0 | 1 -> S.union ocut icut
            | _ -> aux ocut icut trail)
        | Clauses.TImply (l, lits) :: trail when S.mem (Lit.var l) icut -> (
            let ocut, icut =
              lits
              |> ((ocut, icut)
                 |> Array.fold_left (fun (ocut, icut) l' ->
                        if l = l' then (ocut, icut)
                        else
                          let v = Lit.var l' in
                          let level = Assign.level assign v in
                          if level = dlevel then (ocut, icut |> S.add v)
                          else (ocut |> S.add v, icut)))
            in
            let icut = icut |> S.remove (Lit.var l) in
            match S.cardinal icut with
            | 0 | 1 -> S.union ocut icut
            | _ -> aux ocut icut trail)
        | Clauses.TImply (_, _) :: trail -> aux ocut icut trail
        | Clauses.TDecide _ :: trail ->
            assert (List.length trail = 0);
            S.union ocut icut
      in
      let cut = aux ocut icut trail |> S.elements in
      let learnt_clause =
        cut
        |> List.map (fun v ->
               match Assign.value assign v with
               | Assign.True -> Lit.make v |> Lit.neg
               | Assign.False -> Lit.make v
               | Assign.Unknown -> failwith "first_uip_cut: unknown value")
        |> Array.of_list
      in
      let blevel =
        cut
        |> List.fold_left
             (fun acc v ->
               let level = Assign.level assign v in
               if level = dlevel then acc else max acc level)
             0
      in
      (blevel, learnt_clause)
  | _ -> failwith "first_uip_cut: no conflict clause"

let dpll_solve ?(debug = false) ?(watched_literal = true) (cnf : Cnf.t) :
    Cnf.result =
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
      if watched_literal then Clauses.propagate ~debug clauses assign (Some lit)
      else Clauses.full_propagate ~debug clauses assign (Some lit)
    in
    match result with
    | Clauses.Sat -> Cnf.SAT (Assign.to_list assign)
    | Clauses.Conflict _ -> Cnf.UNSAT
    | Clauses.Continue _ -> select (level + 1)
  in
  select 1

let cdcl_solve ?(debug = false) ?(watched_literal = true) (cnf : Cnf.t) :
    Cnf.result =
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
  let propagate =
    if watched_literal then fun d -> Clauses.propagate ~debug clauses assign d
    else fun d -> Clauses.full_propagate ~debug clauses assign d
  in
  let _ = (debug, watched_literal, clauses, assign, score) in
  let rec decide trails level =
    Assign.set_edit_level assign level;
    match Assign.unassigned assign score with
    | None ->
        let assign = Assign.to_list assign in
        if Cnf.assign_is_valid cnf assign then Cnf.SAT assign else Cnf.UNSAT
    | Some v -> (
        let l = Lit.make v |> Lit.neg in
        match propagate (Some l) with
        | Clauses.Sat -> Cnf.SAT (Assign.to_list assign)
        | Clauses.Continue trail -> decide ((level, trail) :: trails) (level + 1)
        | Clauses.Conflict trail ->
            let blevel, learnt_clause = first_uip_cut assign trail in
            Clauses.add_clause clauses learnt_clause;
            backjump trails blevel)
  and backjump trails level =
    Assign.set_edit_level assign level;
    let trail, rest_trails =
      let rec aux = function
        | [] -> ([], [])
        | (l, trail) :: rest when l = level -> (trail, rest)
        | (l, _) :: _ as rest when l < level -> ([], rest)
        | _ :: rest -> aux rest
      in
      aux trails
    in
    match propagate None with
    | Clauses.Sat -> Cnf.SAT (Assign.to_list assign)
    | Clauses.Continue trail' ->
        decide ((level, trail' @ trail) :: rest_trails) (level + 1)
    | Clauses.Conflict trail' ->
        let trail = trail' @ trail in
        let blevel, learnt_clause = first_uip_cut assign trail in
        Clauses.add_clause clauses learnt_clause;
        backjump rest_trails blevel
  in
  decide [] 1
