val dpll_solve : ?debug:bool -> ?watched_literal:bool -> Cnf.t -> Cnf.result

val cdcl_solve : ?debug:bool -> ?watched_literal:bool -> Cnf.t -> Cnf.result