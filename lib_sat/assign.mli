type t
type value = True | False | Unknown

val create : int -> t
val unassigned : t -> (int -> int) -> int option
val value : t -> int -> value
val xor : t -> Lit.t -> value
val to_list : t -> int list
val assign : t -> Lit.t -> unit
val set_level : t -> int -> unit
