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
