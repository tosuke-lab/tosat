type t = int ref * int array (* level * assign *)
type value = True | False | Unknown

let create nvars =
  let level = ref 4 in
  (* level 1 *)
  let assign = Array.make (nvars + 1) 2 in
  (* level 0 unknown*)
  (level, assign)

let nvars (_, a) = Array.length a - 1

let value (_, a) var =
  match a.(var) land 3 with 1 -> True | 0 -> False | _ -> Unknown

let xor (_, a) lit =
  let sign = a.(Lit.var lit) land 3 lxor if Lit.sign lit then 1 else 0 in
  match sign with 1 -> True | 0 -> False | _ -> Unknown

let level (level, _) = !level lsr 2

let unassigned assign score =
  let rec aux acc max_score v =
    if v = 0 then acc
    else if value assign v = Unknown then
      let score_v = score v in
      if score_v > max_score then aux (Some v) score_v (v - 1)
      else aux acc max_score (v - 1)
    else aux acc max_score (v - 1)
  in
  aux None Int.min_int (nvars assign)

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
  a.(Lit.var l) <- x

let set_level assign lev =
  (if lev <= level assign then
     let _, a = assign in
     if lev = 0 then
       for i = 1 to Array.length a - 1 do
         a.(i) <- a.(i) land 3
       done
     else
       let th = ((lev - 1) lsl 2) lor 3 in
       for i = 1 to Array.length a - 1 do
         if a.(i) > th then a.(i) <- 2
       done);

  let cur_level, _ = assign in
  cur_level := lev lsl 2
