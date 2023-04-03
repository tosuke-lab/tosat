type t = { mutable level : int; a : int array }
type value = True | False | Unknown

let create (nvars : int) : t =
  let level = 4 in
  (* level 1 *)
  let assign = Array.make (nvars + 1) 2 in
  (* level 0 unknown*)
  { level; a = assign }

let nvars (assign : t) : int = Array.length assign.a - 1

let value (assign : t) (var : int) : value =
  match assign.a.(var) land 3 with 1 -> True | 0 -> False | _ -> Unknown

let xor (assign : t) (lit : Lit.t) : value =
  let sign = assign.a.(Lit.var lit) land 3 lxor if Lit.sign lit then 1 else 0 in
  match sign with 1 -> True | 0 -> False | _ -> Unknown

let level (assign : t) (var : int) : int = assign.a.(var) lsr 2
let current_level (assign : t) : int = assign.level lsr 2

let unassigned (assign : t) (score : int -> int) : int option =
  let rec aux acc max_score v =
    if v = 0 then acc
    else if value assign v = Unknown then
      let score_v = score v in
      if score_v >= max_score then aux (Some v) score_v (v - 1)
      else aux acc max_score (v - 1)
    else aux acc max_score (v - 1)
  in
  aux None Int.min_int (nvars assign)

let to_list (assign : t) : int list =
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

let assign (assign : t) (l : Lit.t) : unit =
  let x = assign.level lor if Lit.sign l then 1 else 0 in
  assign.a.(Lit.var l) <- x

let set_level (assign : t) (lev : int) : unit =
  (if lev <= current_level assign then
     let a = assign.a in
     if lev = 0 then
       for i = 1 to Array.length a - 1 do
         a.(i) <- a.(i) land 3
       done
     else
       let th = ((lev - 1) lsl 2) lor 3 in
       for i = 1 to Array.length a - 1 do
         if a.(i) > th then a.(i) <- 2
       done);
  assign.level <- lev lsl 2

let set_edit_level (assign : t) (lev : int) : unit =
  (if lev < current_level assign then
     let a = assign.a in
     let th = (lev lsl 2) lor 3 in
     for i = 1 to Array.length a - 1 do
       if a.(i) > th then a.(i) <- 2
     done);
  assign.level <- lev lsl 2
