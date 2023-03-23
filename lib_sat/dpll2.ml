(* fast DPLL implementation *)

module Lit : sig
  type t

  val nil : t
  val make : int -> t
  val neg : t -> t
  val sign : t -> bool
  val var : t -> int
  val to_int : t -> int [@@warning "-32"]
end = struct
  type t = int

  let nil = 0

  let make i =
    let sign = if i > 0 then 0 else 1 in
    let i = abs i in
    (i lsl 1) lor sign

  let neg n = n lxor 1
  let sign l = l land 1 = 0
  let var l = l lsr 1

  let to_int l =
    let sign = if sign l then 1 else -1 in
    var l * sign
end

module Assign : sig
  type t
  type value = True | False | Unknown

  val create : int -> t
  val unassigned : t -> (int -> int) -> int option
  val xor : t -> Lit.t -> value
  val to_list : t -> int list
  val assign : t -> Lit.t -> unit
  val set_level : t -> int -> unit
end = struct
  type t = int ref * int array (* level * assign *)
  type value = True | False | Unknown

  let create nvars =
    let level = ref 4 in
    (* level 1 *)
    let assign = Array.make nvars 2 in
    (* level 0 unknown*)
    (level, assign)

  let nvars (_, a) = Array.length a

  let value (_, a) var =
    match a.(var - 1) land 3 with 1 -> True | 0 -> False | _ -> Unknown

  let xor (_, a) lit =
    let sign = a.(Lit.var lit - 1) land 3 lxor if Lit.sign lit then 1 else 0 in
    match sign with 1 -> True | 0 -> False | _ -> Unknown

  let level (level, _) = !level lsr 2

  let unassigned assign score =
    let nvars = nvars assign in
    let rec aux acc max_score v =
      if v > nvars then acc
      else if value assign v = Unknown then
        let score_v = score v in
        if score_v > max_score then aux (Some v) score_v (v + 1)
        else aux acc max_score (v + 1)
      else aux acc max_score (v + 1)
    in
    aux None Int.min_int 1

  let to_list assign =
    let nvars = nvars assign in
    let rec aux acc v =
      if v = 0 then acc
      else
        match value assign v with
        | True -> aux (v :: acc) (v - 1)
        | False -> aux (-v :: acc) (v - 1)
        | Unknown -> aux acc (v - 1)
    in
    aux [] nvars

  let assign (level, a) l =
    let x = !level lor if Lit.sign l then 1 else 0 in
    a.(Lit.var l - 1) <- x

  let set_level assign lev =
    (if lev <= level assign then
       let _, a = assign in
       if lev = 0 then
         for i = 0 to Array.length a - 1 do
           a.(i) <- a.(i) land 3
         done
       else
         let th = ((lev - 1) lsl 2) lor 3 in
         for i = 0 to Array.length a - 1 do
           if a.(i) > th then a.(i) <- 2
         done);

    let cur_level, _ = assign in
    cur_level := lev lsl 2
end

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
